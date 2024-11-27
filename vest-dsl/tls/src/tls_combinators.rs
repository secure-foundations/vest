#![allow(warnings)]
#![allow(unused_imports)]
use vstd::prelude::*;
use vest::properties::*;
use vest::utils::*;
use vest::regular::map::*;
use vest::regular::tag::*;
use vest::regular::choice::*;
use vest::regular::cond::*;
use vest::regular::uints::*;
use vest::regular::tail::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::*;
use vest::regular::depend::*;
use vest::regular::and_then::*;
use vest::regular::refined::*;
use vest::regular::repeat::*;
verus!{
pub type SpecExtensionType = u16;
pub type ExtensionType = u16;
pub type ExtensionTypeOwned = u16;

pub type SpecUint0Ffff = u16;
pub type Uint0Ffff = u16;
pub type Uint0FfffOwned = u16;

pub struct SpecOpaque0Ffff {
    pub l: SpecUint0Ffff,
    pub data: Seq<u8>,
}
pub type SpecOpaque0FfffInner = (SpecUint0Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque0Ffff> for SpecOpaque0FfffInner {
    open spec fn spec_from(m: SpecOpaque0Ffff) -> SpecOpaque0FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfffInner> for SpecOpaque0Ffff {
    open spec fn spec_from(m: SpecOpaque0FfffInner) -> SpecOpaque0Ffff {
        let (l, data) = m;
        SpecOpaque0Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ffff<'a> {
    pub l: Uint0Ffff,
    pub data: &'a [u8],
}
pub type Opaque0FfffInner<'a> = (Uint0Ffff, &'a [u8]);
impl View for Opaque0Ffff<'_> {
    type V = SpecOpaque0Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ffff<'a>> for Opaque0FfffInner<'a> {
    fn ex_from(m: Opaque0Ffff<'a>) -> Opaque0FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffInner<'a>> for Opaque0Ffff<'a> {
    fn ex_from(m: Opaque0FfffInner<'a>) -> Opaque0Ffff<'a> {
        let (l, data) = m;
        Opaque0Ffff {
            l,
            data,
        }
    }
}
pub struct Opaque0FfffMapper;
impl View for Opaque0FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffMapper {
    type Src = SpecOpaque0FfffInner;
    type Dst = SpecOpaque0Ffff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque0FfffMapper {
    type Src<'a> = Opaque0FfffInner<'a>;
    type Dst<'a> = Opaque0Ffff<'a>;
    type SrcOwned = Opaque0FfffOwnedInner;
    type DstOwned = Opaque0FfffOwned;
}
pub struct Opaque0FfffOwned {
    pub l: Uint0FfffOwned,
    pub data: Vec<u8>,
}
pub type Opaque0FfffOwnedInner = (Uint0FfffOwned, Vec<u8>);
impl View for Opaque0FfffOwned {
    type V = SpecOpaque0Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque0FfffOwned> for Opaque0FfffOwnedInner {
    fn ex_from(m: Opaque0FfffOwned) -> Opaque0FfffOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque0FfffOwnedInner> for Opaque0FfffOwned {
    fn ex_from(m: Opaque0FfffOwnedInner) -> Opaque0FfffOwned {
        let (l, data) = m;
        Opaque0FfffOwned {
            l,
            data,
        }
    }
}

pub struct SpecExtension {
    pub extension_type: SpecExtensionType,
    pub extension_data: SpecOpaque0Ffff,
}
pub type SpecExtensionInner = (SpecExtensionType, SpecOpaque0Ffff);
impl SpecFrom<SpecExtension> for SpecExtensionInner {
    open spec fn spec_from(m: SpecExtension) -> SpecExtensionInner {
        (m.extension_type, m.extension_data)
    }
}
impl SpecFrom<SpecExtensionInner> for SpecExtension {
    open spec fn spec_from(m: SpecExtensionInner) -> SpecExtension {
        let (extension_type, extension_data) = m;
        SpecExtension {
            extension_type,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Extension<'a> {
    pub extension_type: ExtensionType,
    pub extension_data: Opaque0Ffff<'a>,
}
pub type ExtensionInner<'a> = (ExtensionType, Opaque0Ffff<'a>);
impl View for Extension<'_> {
    type V = SpecExtension;
    open spec fn view(&self) -> Self::V {
        SpecExtension {
            extension_type: self.extension_type@,
            extension_data: self.extension_data@,
        }
    }
}
impl<'a> From<Extension<'a>> for ExtensionInner<'a> {
    fn ex_from(m: Extension<'a>) -> ExtensionInner<'a> {
        (m.extension_type, m.extension_data)
    }
}
impl<'a> From<ExtensionInner<'a>> for Extension<'a> {
    fn ex_from(m: ExtensionInner<'a>) -> Extension<'a> {
        let (extension_type, extension_data) = m;
        Extension {
            extension_type,
            extension_data,
        }
    }
}
pub struct ExtensionMapper;
impl View for ExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ExtensionMapper {
    type Src = SpecExtensionInner;
    type Dst = SpecExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ExtensionMapper {
    type Src<'a> = ExtensionInner<'a>;
    type Dst<'a> = Extension<'a>;
    type SrcOwned = ExtensionOwnedInner;
    type DstOwned = ExtensionOwned;
}
pub struct ExtensionOwned {
    pub extension_type: ExtensionTypeOwned,
    pub extension_data: Opaque0FfffOwned,
}
pub type ExtensionOwnedInner = (ExtensionTypeOwned, Opaque0FfffOwned);
impl View for ExtensionOwned {
    type V = SpecExtension;
    open spec fn view(&self) -> Self::V {
        SpecExtension {
            extension_type: self.extension_type@,
            extension_data: self.extension_data@,
        }
    }
}
impl From<ExtensionOwned> for ExtensionOwnedInner {
    fn ex_from(m: ExtensionOwned) -> ExtensionOwnedInner {
        (m.extension_type, m.extension_data)
    }
}
impl From<ExtensionOwnedInner> for ExtensionOwned {
    fn ex_from(m: ExtensionOwnedInner) -> ExtensionOwned {
        let (extension_type, extension_data) = m;
        ExtensionOwned {
            extension_type,
            extension_data,
        }
    }
}

pub type SpecNewSessionTicketExtensionsExtensions = Seq<SpecExtension>;
pub type NewSessionTicketExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;
pub type NewSessionTicketExtensionsExtensionsOwned = RepeatResult<ExtensionOwned>;

pub type SpecProtocolVersion = u16;
pub type ProtocolVersion = u16;
pub type ProtocolVersionOwned = u16;

pub type SpecSupportedVersionsClientVersions = Seq<SpecProtocolVersion>;
pub type SupportedVersionsClientVersions = RepeatResult<ProtocolVersion>;
pub type SupportedVersionsClientVersionsOwned = RepeatResult<ProtocolVersionOwned>;

pub type SpecEcPointFormat = u8;
pub type EcPointFormat = u8;
pub type EcPointFormatOwned = u8;

pub type SpecEcPointFormatListList = Seq<SpecEcPointFormat>;
pub type EcPointFormatListList = RepeatResult<EcPointFormat>;
pub type EcPointFormatListListOwned = RepeatResult<EcPointFormatOwned>;

pub struct SpecZeroByte {
    pub zero: u8,
}
pub type SpecZeroByteInner = u8;
impl SpecFrom<SpecZeroByte> for SpecZeroByteInner {
    open spec fn spec_from(m: SpecZeroByte) -> SpecZeroByteInner {
        m.zero
    }
}
impl SpecFrom<SpecZeroByteInner> for SpecZeroByte {
    open spec fn spec_from(m: SpecZeroByteInner) -> SpecZeroByte {
        let zero = m;
        SpecZeroByte {
            zero,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ZeroByte {
    pub zero: u8,
}
pub type ZeroByteInner = u8;
impl View for ZeroByte {
    type V = SpecZeroByte;
    open spec fn view(&self) -> Self::V {
        SpecZeroByte {
            zero: self.zero@,
        }
    }
}
impl From<ZeroByte> for ZeroByteInner {
    fn ex_from(m: ZeroByte) -> ZeroByteInner {
        m.zero
    }
}
impl From<ZeroByteInner> for ZeroByte {
    fn ex_from(m: ZeroByteInner) -> ZeroByte {
        let zero = m;
        ZeroByte {
            zero,
        }
    }
}
pub struct ZeroByteMapper;
impl View for ZeroByteMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ZeroByteMapper {
    type Src = SpecZeroByteInner;
    type Dst = SpecZeroByte;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ZeroByteMapper {
    type Src<'a> = ZeroByteInner;
    type Dst<'a> = ZeroByte;
    type SrcOwned = ZeroByteOwnedInner;
    type DstOwned = ZeroByteOwned;
}
pub struct ZeroByteOwned {
    pub zero: u8,
}
pub type ZeroByteOwnedInner = u8;
impl View for ZeroByteOwned {
    type V = SpecZeroByte;
    open spec fn view(&self) -> Self::V {
        SpecZeroByte {
            zero: self.zero@,
        }
    }
}
impl From<ZeroByteOwned> for ZeroByteOwnedInner {
    fn ex_from(m: ZeroByteOwned) -> ZeroByteOwnedInner {
        m.zero
    }
}
impl From<ZeroByteOwnedInner> for ZeroByteOwned {
    fn ex_from(m: ZeroByteOwnedInner) -> ZeroByteOwned {
        let zero = m;
        ZeroByteOwned {
            zero,
        }
    }
}

pub type SpecPaddingExtensionPadding = Seq<SpecZeroByte>;
pub type PaddingExtensionPadding = RepeatResult<ZeroByte>;
pub type PaddingExtensionPaddingOwned = RepeatResult<ZeroByteOwned>;

pub type SpecPskKeyExchangeMode = u8;
pub type PskKeyExchangeMode = u8;
pub type PskKeyExchangeModeOwned = u8;

pub type SpecPskKeyExchangeModesModes = Seq<SpecPskKeyExchangeMode>;
pub type PskKeyExchangeModesModes = RepeatResult<PskKeyExchangeMode>;
pub type PskKeyExchangeModesModesOwned = RepeatResult<PskKeyExchangeModeOwned>;

pub type SpecUint1Ffff = u16;
pub type Uint1Ffff = u16;
pub type Uint1FfffOwned = u16;

pub type SpecNameType = u8;
pub type NameType = u8;
pub type NameTypeOwned = u8;

pub struct SpecOpaque1Ffff {
    pub l: SpecUint1Ffff,
    pub data: Seq<u8>,
}
pub type SpecOpaque1FfffInner = (SpecUint1Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque1Ffff> for SpecOpaque1FfffInner {
    open spec fn spec_from(m: SpecOpaque1Ffff) -> SpecOpaque1FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfffInner> for SpecOpaque1Ffff {
    open spec fn spec_from(m: SpecOpaque1FfffInner) -> SpecOpaque1Ffff {
        let (l, data) = m;
        SpecOpaque1Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ffff<'a> {
    pub l: Uint1Ffff,
    pub data: &'a [u8],
}
pub type Opaque1FfffInner<'a> = (Uint1Ffff, &'a [u8]);
impl View for Opaque1Ffff<'_> {
    type V = SpecOpaque1Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ffff<'a>> for Opaque1FfffInner<'a> {
    fn ex_from(m: Opaque1Ffff<'a>) -> Opaque1FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffInner<'a>> for Opaque1Ffff<'a> {
    fn ex_from(m: Opaque1FfffInner<'a>) -> Opaque1Ffff<'a> {
        let (l, data) = m;
        Opaque1Ffff {
            l,
            data,
        }
    }
}
pub struct Opaque1FfffMapper;
impl View for Opaque1FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffMapper {
    type Src = SpecOpaque1FfffInner;
    type Dst = SpecOpaque1Ffff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque1FfffMapper {
    type Src<'a> = Opaque1FfffInner<'a>;
    type Dst<'a> = Opaque1Ffff<'a>;
    type SrcOwned = Opaque1FfffOwnedInner;
    type DstOwned = Opaque1FfffOwned;
}
pub struct Opaque1FfffOwned {
    pub l: Uint1FfffOwned,
    pub data: Vec<u8>,
}
pub type Opaque1FfffOwnedInner = (Uint1FfffOwned, Vec<u8>);
impl View for Opaque1FfffOwned {
    type V = SpecOpaque1Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque1FfffOwned> for Opaque1FfffOwnedInner {
    fn ex_from(m: Opaque1FfffOwned) -> Opaque1FfffOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque1FfffOwnedInner> for Opaque1FfffOwned {
    fn ex_from(m: Opaque1FfffOwnedInner) -> Opaque1FfffOwned {
        let (l, data) = m;
        Opaque1FfffOwned {
            l,
            data,
        }
    }
}

pub type SpecHostName = SpecOpaque1Ffff;
pub type HostName<'a> = Opaque1Ffff<'a>;
pub type HostNameOwned = Opaque1FfffOwned;

pub type SpecUnknownName = SpecOpaque1Ffff;
pub type UnknownName<'a> = Opaque1Ffff<'a>;
pub type UnknownNameOwned = Opaque1FfffOwned;

pub enum SpecServerNameName {
    HostName(SpecHostName),
    Unrecognized(SpecUnknownName),
}
pub type SpecServerNameNameInner = Either<SpecHostName, SpecUnknownName>;
impl SpecFrom<SpecServerNameName> for SpecServerNameNameInner {
    open spec fn spec_from(m: SpecServerNameName) -> SpecServerNameNameInner {
        match m {
            SpecServerNameName::HostName(m) => Either::Left(m),
            SpecServerNameName::Unrecognized(m) => Either::Right(m),
        }
    }
}
impl SpecFrom<SpecServerNameNameInner> for SpecServerNameName {
    open spec fn spec_from(m: SpecServerNameNameInner) -> SpecServerNameName {
        match m {
            Either::Left(m) => SpecServerNameName::HostName(m),
            Either::Right(m) => SpecServerNameName::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ServerNameName<'a> {
    HostName(HostName<'a>),
    Unrecognized(UnknownName<'a>),
}
pub type ServerNameNameInner<'a> = Either<HostName<'a>, UnknownName<'a>>;
impl View for ServerNameName<'_> {
    type V = SpecServerNameName;
    open spec fn view(&self) -> Self::V {
        match self {
            ServerNameName::HostName(m) => SpecServerNameName::HostName(m@),
            ServerNameName::Unrecognized(m) => SpecServerNameName::Unrecognized(m@),
        }
    }
}
impl<'a> From<ServerNameName<'a>> for ServerNameNameInner<'a> {
    fn ex_from(m: ServerNameName<'a>) -> ServerNameNameInner<'a> {
        match m {
            ServerNameName::HostName(m) => Either::Left(m),
            ServerNameName::Unrecognized(m) => Either::Right(m),
        }
    }
}
impl<'a> From<ServerNameNameInner<'a>> for ServerNameName<'a> {
    fn ex_from(m: ServerNameNameInner<'a>) -> ServerNameName<'a> {
        match m {
            Either::Left(m) => ServerNameName::HostName(m),
            Either::Right(m) => ServerNameName::Unrecognized(m),
        }
    }
}
pub struct ServerNameNameMapper;
impl View for ServerNameNameMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameNameMapper {
    type Src = SpecServerNameNameInner;
    type Dst = SpecServerNameName;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerNameNameMapper {
    type Src<'a> = ServerNameNameInner<'a>;
    type Dst<'a> = ServerNameName<'a>;
    type SrcOwned = ServerNameNameOwnedInner;
    type DstOwned = ServerNameNameOwned;
}
pub enum ServerNameNameOwned {
    HostName(HostNameOwned),
    Unrecognized(UnknownNameOwned),
}
pub type ServerNameNameOwnedInner = Either<HostNameOwned, UnknownNameOwned>;
impl View for ServerNameNameOwned {
    type V = SpecServerNameName;
    open spec fn view(&self) -> Self::V {
        match self {
            ServerNameNameOwned::HostName(m) => SpecServerNameName::HostName(m@),
            ServerNameNameOwned::Unrecognized(m) => SpecServerNameName::Unrecognized(m@),
        }
    }
}
impl From<ServerNameNameOwned> for ServerNameNameOwnedInner {
    fn ex_from(m: ServerNameNameOwned) -> ServerNameNameOwnedInner {
        match m {
            ServerNameNameOwned::HostName(m) => Either::Left(m),
            ServerNameNameOwned::Unrecognized(m) => Either::Right(m),
        }
    }
}
impl From<ServerNameNameOwnedInner> for ServerNameNameOwned {
    fn ex_from(m: ServerNameNameOwnedInner) -> ServerNameNameOwned {
        match m {
            Either::Left(m) => ServerNameNameOwned::HostName(m),
            Either::Right(m) => ServerNameNameOwned::Unrecognized(m),
        }
    }
}

pub struct SpecServerName {
    pub name_type: SpecNameType,
    pub name: SpecServerNameName,
}
pub type SpecServerNameInner = (SpecNameType, SpecServerNameName);
impl SpecFrom<SpecServerName> for SpecServerNameInner {
    open spec fn spec_from(m: SpecServerName) -> SpecServerNameInner {
        (m.name_type, m.name)
    }
}
impl SpecFrom<SpecServerNameInner> for SpecServerName {
    open spec fn spec_from(m: SpecServerNameInner) -> SpecServerName {
        let (name_type, name) = m;
        SpecServerName {
            name_type,
            name,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerName<'a> {
    pub name_type: NameType,
    pub name: ServerNameName<'a>,
}
pub type ServerNameInner<'a> = (NameType, ServerNameName<'a>);
impl View for ServerName<'_> {
    type V = SpecServerName;
    open spec fn view(&self) -> Self::V {
        SpecServerName {
            name_type: self.name_type@,
            name: self.name@,
        }
    }
}
impl<'a> From<ServerName<'a>> for ServerNameInner<'a> {
    fn ex_from(m: ServerName<'a>) -> ServerNameInner<'a> {
        (m.name_type, m.name)
    }
}
impl<'a> From<ServerNameInner<'a>> for ServerName<'a> {
    fn ex_from(m: ServerNameInner<'a>) -> ServerName<'a> {
        let (name_type, name) = m;
        ServerName {
            name_type,
            name,
        }
    }
}
pub struct ServerNameMapper;
impl View for ServerNameMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameMapper {
    type Src = SpecServerNameInner;
    type Dst = SpecServerName;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerNameMapper {
    type Src<'a> = ServerNameInner<'a>;
    type Dst<'a> = ServerName<'a>;
    type SrcOwned = ServerNameOwnedInner;
    type DstOwned = ServerNameOwned;
}
pub struct ServerNameOwned {
    pub name_type: NameTypeOwned,
    pub name: ServerNameNameOwned,
}
pub type ServerNameOwnedInner = (NameTypeOwned, ServerNameNameOwned);
impl View for ServerNameOwned {
    type V = SpecServerName;
    open spec fn view(&self) -> Self::V {
        SpecServerName {
            name_type: self.name_type@,
            name: self.name@,
        }
    }
}
impl From<ServerNameOwned> for ServerNameOwnedInner {
    fn ex_from(m: ServerNameOwned) -> ServerNameOwnedInner {
        (m.name_type, m.name)
    }
}
impl From<ServerNameOwnedInner> for ServerNameOwned {
    fn ex_from(m: ServerNameOwnedInner) -> ServerNameOwned {
        let (name_type, name) = m;
        ServerNameOwned {
            name_type,
            name,
        }
    }
}

pub type SpecServerNameListList = Seq<SpecServerName>;
pub type ServerNameListList<'a> = RepeatResult<ServerName<'a>>;
pub type ServerNameListListOwned = RepeatResult<ServerNameOwned>;

pub struct SpecServerNameList {
    pub l: SpecUint1Ffff,
    pub list: SpecServerNameListList,
}
pub type SpecServerNameListInner = (SpecUint1Ffff, SpecServerNameListList);
impl SpecFrom<SpecServerNameList> for SpecServerNameListInner {
    open spec fn spec_from(m: SpecServerNameList) -> SpecServerNameListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecServerNameListInner> for SpecServerNameList {
    open spec fn spec_from(m: SpecServerNameListInner) -> SpecServerNameList {
        let (l, list) = m;
        SpecServerNameList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerNameList<'a> {
    pub l: Uint1Ffff,
    pub list: ServerNameListList<'a>,
}
pub type ServerNameListInner<'a> = (Uint1Ffff, ServerNameListList<'a>);
impl View for ServerNameList<'_> {
    type V = SpecServerNameList;
    open spec fn view(&self) -> Self::V {
        SpecServerNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<ServerNameList<'a>> for ServerNameListInner<'a> {
    fn ex_from(m: ServerNameList<'a>) -> ServerNameListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<ServerNameListInner<'a>> for ServerNameList<'a> {
    fn ex_from(m: ServerNameListInner<'a>) -> ServerNameList<'a> {
        let (l, list) = m;
        ServerNameList {
            l,
            list,
        }
    }
}
pub struct ServerNameListMapper;
impl View for ServerNameListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerNameListMapper {
    type Src = SpecServerNameListInner;
    type Dst = SpecServerNameList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerNameListMapper {
    type Src<'a> = ServerNameListInner<'a>;
    type Dst<'a> = ServerNameList<'a>;
    type SrcOwned = ServerNameListOwnedInner;
    type DstOwned = ServerNameListOwned;
}
pub struct ServerNameListOwned {
    pub l: Uint1FfffOwned,
    pub list: ServerNameListListOwned,
}
pub type ServerNameListOwnedInner = (Uint1FfffOwned, ServerNameListListOwned);
impl View for ServerNameListOwned {
    type V = SpecServerNameList;
    open spec fn view(&self) -> Self::V {
        SpecServerNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<ServerNameListOwned> for ServerNameListOwnedInner {
    fn ex_from(m: ServerNameListOwned) -> ServerNameListOwnedInner {
        (m.l, m.list)
    }
}
impl From<ServerNameListOwnedInner> for ServerNameListOwned {
    fn ex_from(m: ServerNameListOwnedInner) -> ServerNameListOwned {
        let (l, list) = m;
        ServerNameListOwned {
            l,
            list,
        }
    }
}

pub type SpecMaxFragmentLength = u8;
pub type MaxFragmentLength = u8;
pub type MaxFragmentLengthOwned = u8;

pub type SpecResponderId = SpecOpaque1Ffff;
pub type ResponderId<'a> = Opaque1Ffff<'a>;
pub type ResponderIdOwned = Opaque1FfffOwned;

pub type SpecResponderIdListList = Seq<SpecResponderId>;
pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;
pub type ResponderIdListListOwned = RepeatResult<ResponderIdOwned>;

pub struct SpecResponderIdList {
    pub l: SpecUint0Ffff,
    pub list: SpecResponderIdListList,
}
pub type SpecResponderIdListInner = (SpecUint0Ffff, SpecResponderIdListList);
impl SpecFrom<SpecResponderIdList> for SpecResponderIdListInner {
    open spec fn spec_from(m: SpecResponderIdList) -> SpecResponderIdListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecResponderIdListInner> for SpecResponderIdList {
    open spec fn spec_from(m: SpecResponderIdListInner) -> SpecResponderIdList {
        let (l, list) = m;
        SpecResponderIdList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResponderIdList<'a> {
    pub l: Uint0Ffff,
    pub list: ResponderIdListList<'a>,
}
pub type ResponderIdListInner<'a> = (Uint0Ffff, ResponderIdListList<'a>);
impl View for ResponderIdList<'_> {
    type V = SpecResponderIdList;
    open spec fn view(&self) -> Self::V {
        SpecResponderIdList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<ResponderIdList<'a>> for ResponderIdListInner<'a> {
    fn ex_from(m: ResponderIdList<'a>) -> ResponderIdListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<ResponderIdListInner<'a>> for ResponderIdList<'a> {
    fn ex_from(m: ResponderIdListInner<'a>) -> ResponderIdList<'a> {
        let (l, list) = m;
        ResponderIdList {
            l,
            list,
        }
    }
}
pub struct ResponderIdListMapper;
impl View for ResponderIdListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ResponderIdListMapper {
    type Src = SpecResponderIdListInner;
    type Dst = SpecResponderIdList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ResponderIdListMapper {
    type Src<'a> = ResponderIdListInner<'a>;
    type Dst<'a> = ResponderIdList<'a>;
    type SrcOwned = ResponderIdListOwnedInner;
    type DstOwned = ResponderIdListOwned;
}
pub struct ResponderIdListOwned {
    pub l: Uint0FfffOwned,
    pub list: ResponderIdListListOwned,
}
pub type ResponderIdListOwnedInner = (Uint0FfffOwned, ResponderIdListListOwned);
impl View for ResponderIdListOwned {
    type V = SpecResponderIdList;
    open spec fn view(&self) -> Self::V {
        SpecResponderIdList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<ResponderIdListOwned> for ResponderIdListOwnedInner {
    fn ex_from(m: ResponderIdListOwned) -> ResponderIdListOwnedInner {
        (m.l, m.list)
    }
}
impl From<ResponderIdListOwnedInner> for ResponderIdListOwned {
    fn ex_from(m: ResponderIdListOwnedInner) -> ResponderIdListOwned {
        let (l, list) = m;
        ResponderIdListOwned {
            l,
            list,
        }
    }
}

pub type SpecOcspExtensions = SpecOpaque0Ffff;
pub type OcspExtensions<'a> = Opaque0Ffff<'a>;
pub type OcspExtensionsOwned = Opaque0FfffOwned;

pub struct SpecOscpStatusRequest {
    pub responder_id_list: SpecResponderIdList,
    pub extensions: SpecOcspExtensions,
}
pub type SpecOscpStatusRequestInner = (SpecResponderIdList, SpecOcspExtensions);
impl SpecFrom<SpecOscpStatusRequest> for SpecOscpStatusRequestInner {
    open spec fn spec_from(m: SpecOscpStatusRequest) -> SpecOscpStatusRequestInner {
        (m.responder_id_list, m.extensions)
    }
}
impl SpecFrom<SpecOscpStatusRequestInner> for SpecOscpStatusRequest {
    open spec fn spec_from(m: SpecOscpStatusRequestInner) -> SpecOscpStatusRequest {
        let (responder_id_list, extensions) = m;
        SpecOscpStatusRequest {
            responder_id_list,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OscpStatusRequest<'a> {
    pub responder_id_list: ResponderIdList<'a>,
    pub extensions: OcspExtensions<'a>,
}
pub type OscpStatusRequestInner<'a> = (ResponderIdList<'a>, OcspExtensions<'a>);
impl View for OscpStatusRequest<'_> {
    type V = SpecOscpStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecOscpStatusRequest {
            responder_id_list: self.responder_id_list@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<OscpStatusRequest<'a>> for OscpStatusRequestInner<'a> {
    fn ex_from(m: OscpStatusRequest<'a>) -> OscpStatusRequestInner<'a> {
        (m.responder_id_list, m.extensions)
    }
}
impl<'a> From<OscpStatusRequestInner<'a>> for OscpStatusRequest<'a> {
    fn ex_from(m: OscpStatusRequestInner<'a>) -> OscpStatusRequest<'a> {
        let (responder_id_list, extensions) = m;
        OscpStatusRequest {
            responder_id_list,
            extensions,
        }
    }
}
pub struct OscpStatusRequestMapper;
impl View for OscpStatusRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OscpStatusRequestMapper {
    type Src = SpecOscpStatusRequestInner;
    type Dst = SpecOscpStatusRequest;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for OscpStatusRequestMapper {
    type Src<'a> = OscpStatusRequestInner<'a>;
    type Dst<'a> = OscpStatusRequest<'a>;
    type SrcOwned = OscpStatusRequestOwnedInner;
    type DstOwned = OscpStatusRequestOwned;
}
pub struct OscpStatusRequestOwned {
    pub responder_id_list: ResponderIdListOwned,
    pub extensions: OcspExtensionsOwned,
}
pub type OscpStatusRequestOwnedInner = (ResponderIdListOwned, OcspExtensionsOwned);
impl View for OscpStatusRequestOwned {
    type V = SpecOscpStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecOscpStatusRequest {
            responder_id_list: self.responder_id_list@,
            extensions: self.extensions@,
        }
    }
}
impl From<OscpStatusRequestOwned> for OscpStatusRequestOwnedInner {
    fn ex_from(m: OscpStatusRequestOwned) -> OscpStatusRequestOwnedInner {
        (m.responder_id_list, m.extensions)
    }
}
impl From<OscpStatusRequestOwnedInner> for OscpStatusRequestOwned {
    fn ex_from(m: OscpStatusRequestOwnedInner) -> OscpStatusRequestOwned {
        let (responder_id_list, extensions) = m;
        OscpStatusRequestOwned {
            responder_id_list,
            extensions,
        }
    }
}

pub struct SpecCertificateStatusRequest {
    pub status_type: u8,
    pub request: SpecOscpStatusRequest,
}
pub type SpecCertificateStatusRequestInner = (u8, SpecOscpStatusRequest);
impl SpecFrom<SpecCertificateStatusRequest> for SpecCertificateStatusRequestInner {
    open spec fn spec_from(m: SpecCertificateStatusRequest) -> SpecCertificateStatusRequestInner {
        (m.status_type, m.request)
    }
}
impl SpecFrom<SpecCertificateStatusRequestInner> for SpecCertificateStatusRequest {
    open spec fn spec_from(m: SpecCertificateStatusRequestInner) -> SpecCertificateStatusRequest {
        let (status_type, request) = m;
        SpecCertificateStatusRequest {
            status_type,
            request,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateStatusRequest<'a> {
    pub status_type: u8,
    pub request: OscpStatusRequest<'a>,
}
pub type CertificateStatusRequestInner<'a> = (u8, OscpStatusRequest<'a>);
impl View for CertificateStatusRequest<'_> {
    type V = SpecCertificateStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatusRequest {
            status_type: self.status_type@,
            request: self.request@,
        }
    }
}
impl<'a> From<CertificateStatusRequest<'a>> for CertificateStatusRequestInner<'a> {
    fn ex_from(m: CertificateStatusRequest<'a>) -> CertificateStatusRequestInner<'a> {
        (m.status_type, m.request)
    }
}
impl<'a> From<CertificateStatusRequestInner<'a>> for CertificateStatusRequest<'a> {
    fn ex_from(m: CertificateStatusRequestInner<'a>) -> CertificateStatusRequest<'a> {
        let (status_type, request) = m;
        CertificateStatusRequest {
            status_type,
            request,
        }
    }
}
pub struct CertificateStatusRequestMapper;
impl View for CertificateStatusRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusRequestMapper {
    type Src = SpecCertificateStatusRequestInner;
    type Dst = SpecCertificateStatusRequest;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateStatusRequestMapper {
    type Src<'a> = CertificateStatusRequestInner<'a>;
    type Dst<'a> = CertificateStatusRequest<'a>;
    type SrcOwned = CertificateStatusRequestOwnedInner;
    type DstOwned = CertificateStatusRequestOwned;
}
pub struct CertificateStatusRequestOwned {
    pub status_type: u8,
    pub request: OscpStatusRequestOwned,
}
pub type CertificateStatusRequestOwnedInner = (u8, OscpStatusRequestOwned);
impl View for CertificateStatusRequestOwned {
    type V = SpecCertificateStatusRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatusRequest {
            status_type: self.status_type@,
            request: self.request@,
        }
    }
}
impl From<CertificateStatusRequestOwned> for CertificateStatusRequestOwnedInner {
    fn ex_from(m: CertificateStatusRequestOwned) -> CertificateStatusRequestOwnedInner {
        (m.status_type, m.request)
    }
}
impl From<CertificateStatusRequestOwnedInner> for CertificateStatusRequestOwned {
    fn ex_from(m: CertificateStatusRequestOwnedInner) -> CertificateStatusRequestOwned {
        let (status_type, request) = m;
        CertificateStatusRequestOwned {
            status_type,
            request,
        }
    }
}

pub type SpecUint2Ffff = u16;
pub type Uint2Ffff = u16;
pub type Uint2FfffOwned = u16;

pub type SpecNamedGroup = u16;
pub type NamedGroup = u16;
pub type NamedGroupOwned = u16;

pub type SpecNamedGroupListList = Seq<SpecNamedGroup>;
pub type NamedGroupListList = RepeatResult<NamedGroup>;
pub type NamedGroupListListOwned = RepeatResult<NamedGroupOwned>;

pub struct SpecNamedGroupList {
    pub l: SpecUint2Ffff,
    pub list: SpecNamedGroupListList,
}
pub type SpecNamedGroupListInner = (SpecUint2Ffff, SpecNamedGroupListList);
impl SpecFrom<SpecNamedGroupList> for SpecNamedGroupListInner {
    open spec fn spec_from(m: SpecNamedGroupList) -> SpecNamedGroupListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecNamedGroupListInner> for SpecNamedGroupList {
    open spec fn spec_from(m: SpecNamedGroupListInner) -> SpecNamedGroupList {
        let (l, list) = m;
        SpecNamedGroupList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedGroupList {
    pub l: Uint2Ffff,
    pub list: NamedGroupListList,
}
pub type NamedGroupListInner = (Uint2Ffff, NamedGroupListList);
impl View for NamedGroupList {
    type V = SpecNamedGroupList;
    open spec fn view(&self) -> Self::V {
        SpecNamedGroupList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<NamedGroupList> for NamedGroupListInner {
    fn ex_from(m: NamedGroupList) -> NamedGroupListInner {
        (m.l, m.list)
    }
}
impl From<NamedGroupListInner> for NamedGroupList {
    fn ex_from(m: NamedGroupListInner) -> NamedGroupList {
        let (l, list) = m;
        NamedGroupList {
            l,
            list,
        }
    }
}
pub struct NamedGroupListMapper;
impl View for NamedGroupListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NamedGroupListMapper {
    type Src = SpecNamedGroupListInner;
    type Dst = SpecNamedGroupList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for NamedGroupListMapper {
    type Src<'a> = NamedGroupListInner;
    type Dst<'a> = NamedGroupList;
    type SrcOwned = NamedGroupListOwnedInner;
    type DstOwned = NamedGroupListOwned;
}
pub struct NamedGroupListOwned {
    pub l: Uint2FfffOwned,
    pub list: NamedGroupListListOwned,
}
pub type NamedGroupListOwnedInner = (Uint2FfffOwned, NamedGroupListListOwned);
impl View for NamedGroupListOwned {
    type V = SpecNamedGroupList;
    open spec fn view(&self) -> Self::V {
        SpecNamedGroupList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<NamedGroupListOwned> for NamedGroupListOwnedInner {
    fn ex_from(m: NamedGroupListOwned) -> NamedGroupListOwnedInner {
        (m.l, m.list)
    }
}
impl From<NamedGroupListOwnedInner> for NamedGroupListOwned {
    fn ex_from(m: NamedGroupListOwnedInner) -> NamedGroupListOwned {
        let (l, list) = m;
        NamedGroupListOwned {
            l,
            list,
        }
    }
}

pub type SpecUint1Ff = u8;
pub type Uint1Ff = u8;
pub type Uint1FfOwned = u8;

pub struct SpecEcPointFormatList {
    pub l: SpecUint1Ff,
    pub list: SpecEcPointFormatListList,
}
pub type SpecEcPointFormatListInner = (SpecUint1Ff, SpecEcPointFormatListList);
impl SpecFrom<SpecEcPointFormatList> for SpecEcPointFormatListInner {
    open spec fn spec_from(m: SpecEcPointFormatList) -> SpecEcPointFormatListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecEcPointFormatListInner> for SpecEcPointFormatList {
    open spec fn spec_from(m: SpecEcPointFormatListInner) -> SpecEcPointFormatList {
        let (l, list) = m;
        SpecEcPointFormatList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EcPointFormatList {
    pub l: Uint1Ff,
    pub list: EcPointFormatListList,
}
pub type EcPointFormatListInner = (Uint1Ff, EcPointFormatListList);
impl View for EcPointFormatList {
    type V = SpecEcPointFormatList;
    open spec fn view(&self) -> Self::V {
        SpecEcPointFormatList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<EcPointFormatList> for EcPointFormatListInner {
    fn ex_from(m: EcPointFormatList) -> EcPointFormatListInner {
        (m.l, m.list)
    }
}
impl From<EcPointFormatListInner> for EcPointFormatList {
    fn ex_from(m: EcPointFormatListInner) -> EcPointFormatList {
        let (l, list) = m;
        EcPointFormatList {
            l,
            list,
        }
    }
}
pub struct EcPointFormatListMapper;
impl View for EcPointFormatListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EcPointFormatListMapper {
    type Src = SpecEcPointFormatListInner;
    type Dst = SpecEcPointFormatList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for EcPointFormatListMapper {
    type Src<'a> = EcPointFormatListInner;
    type Dst<'a> = EcPointFormatList;
    type SrcOwned = EcPointFormatListOwnedInner;
    type DstOwned = EcPointFormatListOwned;
}
pub struct EcPointFormatListOwned {
    pub l: Uint1FfOwned,
    pub list: EcPointFormatListListOwned,
}
pub type EcPointFormatListOwnedInner = (Uint1FfOwned, EcPointFormatListListOwned);
impl View for EcPointFormatListOwned {
    type V = SpecEcPointFormatList;
    open spec fn view(&self) -> Self::V {
        SpecEcPointFormatList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<EcPointFormatListOwned> for EcPointFormatListOwnedInner {
    fn ex_from(m: EcPointFormatListOwned) -> EcPointFormatListOwnedInner {
        (m.l, m.list)
    }
}
impl From<EcPointFormatListOwnedInner> for EcPointFormatListOwned {
    fn ex_from(m: EcPointFormatListOwnedInner) -> EcPointFormatListOwned {
        let (l, list) = m;
        EcPointFormatListOwned {
            l,
            list,
        }
    }
}

pub type SpecUint2Fffe = u16;
pub type Uint2Fffe = u16;
pub type Uint2FffeOwned = u16;

pub type SpecSignatureScheme = u16;
pub type SignatureScheme = u16;
pub type SignatureSchemeOwned = u16;

pub type SpecSignatureSchemeListList = Seq<SpecSignatureScheme>;
pub type SignatureSchemeListList = RepeatResult<SignatureScheme>;
pub type SignatureSchemeListListOwned = RepeatResult<SignatureSchemeOwned>;

pub struct SpecSignatureSchemeList {
    pub l: SpecUint2Fffe,
    pub list: SpecSignatureSchemeListList,
}
pub type SpecSignatureSchemeListInner = (SpecUint2Fffe, SpecSignatureSchemeListList);
impl SpecFrom<SpecSignatureSchemeList> for SpecSignatureSchemeListInner {
    open spec fn spec_from(m: SpecSignatureSchemeList) -> SpecSignatureSchemeListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSignatureSchemeListInner> for SpecSignatureSchemeList {
    open spec fn spec_from(m: SpecSignatureSchemeListInner) -> SpecSignatureSchemeList {
        let (l, list) = m;
        SpecSignatureSchemeList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignatureSchemeList {
    pub l: Uint2Fffe,
    pub list: SignatureSchemeListList,
}
pub type SignatureSchemeListInner = (Uint2Fffe, SignatureSchemeListList);
impl View for SignatureSchemeList {
    type V = SpecSignatureSchemeList;
    open spec fn view(&self) -> Self::V {
        SpecSignatureSchemeList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<SignatureSchemeList> for SignatureSchemeListInner {
    fn ex_from(m: SignatureSchemeList) -> SignatureSchemeListInner {
        (m.l, m.list)
    }
}
impl From<SignatureSchemeListInner> for SignatureSchemeList {
    fn ex_from(m: SignatureSchemeListInner) -> SignatureSchemeList {
        let (l, list) = m;
        SignatureSchemeList {
            l,
            list,
        }
    }
}
pub struct SignatureSchemeListMapper;
impl View for SignatureSchemeListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignatureSchemeListMapper {
    type Src = SpecSignatureSchemeListInner;
    type Dst = SpecSignatureSchemeList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SignatureSchemeListMapper {
    type Src<'a> = SignatureSchemeListInner;
    type Dst<'a> = SignatureSchemeList;
    type SrcOwned = SignatureSchemeListOwnedInner;
    type DstOwned = SignatureSchemeListOwned;
}
pub struct SignatureSchemeListOwned {
    pub l: Uint2FffeOwned,
    pub list: SignatureSchemeListListOwned,
}
pub type SignatureSchemeListOwnedInner = (Uint2FffeOwned, SignatureSchemeListListOwned);
impl View for SignatureSchemeListOwned {
    type V = SpecSignatureSchemeList;
    open spec fn view(&self) -> Self::V {
        SpecSignatureSchemeList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<SignatureSchemeListOwned> for SignatureSchemeListOwnedInner {
    fn ex_from(m: SignatureSchemeListOwned) -> SignatureSchemeListOwnedInner {
        (m.l, m.list)
    }
}
impl From<SignatureSchemeListOwnedInner> for SignatureSchemeListOwned {
    fn ex_from(m: SignatureSchemeListOwnedInner) -> SignatureSchemeListOwned {
        let (l, list) = m;
        SignatureSchemeListOwned {
            l,
            list,
        }
    }
}

pub type SpecSrtpProtectionProfile = Seq<u8>;
pub type SrtpProtectionProfile<'a> = &'a [u8];
pub type SrtpProtectionProfileOwned = Vec<u8>;

pub type SpecSrtpProtectionProfilesList = Seq<SpecSrtpProtectionProfile>;
pub type SrtpProtectionProfilesList<'a> = RepeatResult<SrtpProtectionProfile<'a>>;
pub type SrtpProtectionProfilesListOwned = RepeatResult<SrtpProtectionProfileOwned>;

pub struct SpecSrtpProtectionProfiles {
    pub l: SpecUint2Ffff,
    pub list: SpecSrtpProtectionProfilesList,
}
pub type SpecSrtpProtectionProfilesInner = (SpecUint2Ffff, SpecSrtpProtectionProfilesList);
impl SpecFrom<SpecSrtpProtectionProfiles> for SpecSrtpProtectionProfilesInner {
    open spec fn spec_from(m: SpecSrtpProtectionProfiles) -> SpecSrtpProtectionProfilesInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSrtpProtectionProfilesInner> for SpecSrtpProtectionProfiles {
    open spec fn spec_from(m: SpecSrtpProtectionProfilesInner) -> SpecSrtpProtectionProfiles {
        let (l, list) = m;
        SpecSrtpProtectionProfiles {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SrtpProtectionProfiles<'a> {
    pub l: Uint2Ffff,
    pub list: SrtpProtectionProfilesList<'a>,
}
pub type SrtpProtectionProfilesInner<'a> = (Uint2Ffff, SrtpProtectionProfilesList<'a>);
impl View for SrtpProtectionProfiles<'_> {
    type V = SpecSrtpProtectionProfiles;
    open spec fn view(&self) -> Self::V {
        SpecSrtpProtectionProfiles {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<SrtpProtectionProfiles<'a>> for SrtpProtectionProfilesInner<'a> {
    fn ex_from(m: SrtpProtectionProfiles<'a>) -> SrtpProtectionProfilesInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<SrtpProtectionProfilesInner<'a>> for SrtpProtectionProfiles<'a> {
    fn ex_from(m: SrtpProtectionProfilesInner<'a>) -> SrtpProtectionProfiles<'a> {
        let (l, list) = m;
        SrtpProtectionProfiles {
            l,
            list,
        }
    }
}
pub struct SrtpProtectionProfilesMapper;
impl View for SrtpProtectionProfilesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SrtpProtectionProfilesMapper {
    type Src = SpecSrtpProtectionProfilesInner;
    type Dst = SpecSrtpProtectionProfiles;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SrtpProtectionProfilesMapper {
    type Src<'a> = SrtpProtectionProfilesInner<'a>;
    type Dst<'a> = SrtpProtectionProfiles<'a>;
    type SrcOwned = SrtpProtectionProfilesOwnedInner;
    type DstOwned = SrtpProtectionProfilesOwned;
}
pub struct SrtpProtectionProfilesOwned {
    pub l: Uint2FfffOwned,
    pub list: SrtpProtectionProfilesListOwned,
}
pub type SrtpProtectionProfilesOwnedInner = (Uint2FfffOwned, SrtpProtectionProfilesListOwned);
impl View for SrtpProtectionProfilesOwned {
    type V = SpecSrtpProtectionProfiles;
    open spec fn view(&self) -> Self::V {
        SpecSrtpProtectionProfiles {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<SrtpProtectionProfilesOwned> for SrtpProtectionProfilesOwnedInner {
    fn ex_from(m: SrtpProtectionProfilesOwned) -> SrtpProtectionProfilesOwnedInner {
        (m.l, m.list)
    }
}
impl From<SrtpProtectionProfilesOwnedInner> for SrtpProtectionProfilesOwned {
    fn ex_from(m: SrtpProtectionProfilesOwnedInner) -> SrtpProtectionProfilesOwned {
        let (l, list) = m;
        SrtpProtectionProfilesOwned {
            l,
            list,
        }
    }
}

pub type SpecUint0Ff = u8;
pub type Uint0Ff = u8;
pub type Uint0FfOwned = u8;

pub struct SpecOpaque0Ff {
    pub l: SpecUint0Ff,
    pub data: Seq<u8>,
}
pub type SpecOpaque0FfInner = (SpecUint0Ff, Seq<u8>);
impl SpecFrom<SpecOpaque0Ff> for SpecOpaque0FfInner {
    open spec fn spec_from(m: SpecOpaque0Ff) -> SpecOpaque0FfInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfInner> for SpecOpaque0Ff {
    open spec fn spec_from(m: SpecOpaque0FfInner) -> SpecOpaque0Ff {
        let (l, data) = m;
        SpecOpaque0Ff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ff<'a> {
    pub l: Uint0Ff,
    pub data: &'a [u8],
}
pub type Opaque0FfInner<'a> = (Uint0Ff, &'a [u8]);
impl View for Opaque0Ff<'_> {
    type V = SpecOpaque0Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ff<'a>> for Opaque0FfInner<'a> {
    fn ex_from(m: Opaque0Ff<'a>) -> Opaque0FfInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfInner<'a>> for Opaque0Ff<'a> {
    fn ex_from(m: Opaque0FfInner<'a>) -> Opaque0Ff<'a> {
        let (l, data) = m;
        Opaque0Ff {
            l,
            data,
        }
    }
}
pub struct Opaque0FfMapper;
impl View for Opaque0FfMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfMapper {
    type Src = SpecOpaque0FfInner;
    type Dst = SpecOpaque0Ff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque0FfMapper {
    type Src<'a> = Opaque0FfInner<'a>;
    type Dst<'a> = Opaque0Ff<'a>;
    type SrcOwned = Opaque0FfOwnedInner;
    type DstOwned = Opaque0FfOwned;
}
pub struct Opaque0FfOwned {
    pub l: Uint0FfOwned,
    pub data: Vec<u8>,
}
pub type Opaque0FfOwnedInner = (Uint0FfOwned, Vec<u8>);
impl View for Opaque0FfOwned {
    type V = SpecOpaque0Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque0FfOwned> for Opaque0FfOwnedInner {
    fn ex_from(m: Opaque0FfOwned) -> Opaque0FfOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque0FfOwnedInner> for Opaque0FfOwned {
    fn ex_from(m: Opaque0FfOwnedInner) -> Opaque0FfOwned {
        let (l, data) = m;
        Opaque0FfOwned {
            l,
            data,
        }
    }
}

pub struct SpecUseSrtpData {
    pub profiles: SpecSrtpProtectionProfiles,
    pub srtp_mki: SpecOpaque0Ff,
}
pub type SpecUseSrtpDataInner = (SpecSrtpProtectionProfiles, SpecOpaque0Ff);
impl SpecFrom<SpecUseSrtpData> for SpecUseSrtpDataInner {
    open spec fn spec_from(m: SpecUseSrtpData) -> SpecUseSrtpDataInner {
        (m.profiles, m.srtp_mki)
    }
}
impl SpecFrom<SpecUseSrtpDataInner> for SpecUseSrtpData {
    open spec fn spec_from(m: SpecUseSrtpDataInner) -> SpecUseSrtpData {
        let (profiles, srtp_mki) = m;
        SpecUseSrtpData {
            profiles,
            srtp_mki,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseSrtpData<'a> {
    pub profiles: SrtpProtectionProfiles<'a>,
    pub srtp_mki: Opaque0Ff<'a>,
}
pub type UseSrtpDataInner<'a> = (SrtpProtectionProfiles<'a>, Opaque0Ff<'a>);
impl View for UseSrtpData<'_> {
    type V = SpecUseSrtpData;
    open spec fn view(&self) -> Self::V {
        SpecUseSrtpData {
            profiles: self.profiles@,
            srtp_mki: self.srtp_mki@,
        }
    }
}
impl<'a> From<UseSrtpData<'a>> for UseSrtpDataInner<'a> {
    fn ex_from(m: UseSrtpData<'a>) -> UseSrtpDataInner<'a> {
        (m.profiles, m.srtp_mki)
    }
}
impl<'a> From<UseSrtpDataInner<'a>> for UseSrtpData<'a> {
    fn ex_from(m: UseSrtpDataInner<'a>) -> UseSrtpData<'a> {
        let (profiles, srtp_mki) = m;
        UseSrtpData {
            profiles,
            srtp_mki,
        }
    }
}
pub struct UseSrtpDataMapper;
impl View for UseSrtpDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UseSrtpDataMapper {
    type Src = SpecUseSrtpDataInner;
    type Dst = SpecUseSrtpData;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for UseSrtpDataMapper {
    type Src<'a> = UseSrtpDataInner<'a>;
    type Dst<'a> = UseSrtpData<'a>;
    type SrcOwned = UseSrtpDataOwnedInner;
    type DstOwned = UseSrtpDataOwned;
}
pub struct UseSrtpDataOwned {
    pub profiles: SrtpProtectionProfilesOwned,
    pub srtp_mki: Opaque0FfOwned,
}
pub type UseSrtpDataOwnedInner = (SrtpProtectionProfilesOwned, Opaque0FfOwned);
impl View for UseSrtpDataOwned {
    type V = SpecUseSrtpData;
    open spec fn view(&self) -> Self::V {
        SpecUseSrtpData {
            profiles: self.profiles@,
            srtp_mki: self.srtp_mki@,
        }
    }
}
impl From<UseSrtpDataOwned> for UseSrtpDataOwnedInner {
    fn ex_from(m: UseSrtpDataOwned) -> UseSrtpDataOwnedInner {
        (m.profiles, m.srtp_mki)
    }
}
impl From<UseSrtpDataOwnedInner> for UseSrtpDataOwned {
    fn ex_from(m: UseSrtpDataOwnedInner) -> UseSrtpDataOwned {
        let (profiles, srtp_mki) = m;
        UseSrtpDataOwned {
            profiles,
            srtp_mki,
        }
    }
}

pub type SpecHeartbeatMode = u8;
pub type HeartbeatMode = u8;
pub type HeartbeatModeOwned = u8;

pub struct SpecOpaque1Ff {
    pub l: SpecUint1Ff,
    pub data: Seq<u8>,
}
pub type SpecOpaque1FfInner = (SpecUint1Ff, Seq<u8>);
impl SpecFrom<SpecOpaque1Ff> for SpecOpaque1FfInner {
    open spec fn spec_from(m: SpecOpaque1Ff) -> SpecOpaque1FfInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfInner> for SpecOpaque1Ff {
    open spec fn spec_from(m: SpecOpaque1FfInner) -> SpecOpaque1Ff {
        let (l, data) = m;
        SpecOpaque1Ff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ff<'a> {
    pub l: Uint1Ff,
    pub data: &'a [u8],
}
pub type Opaque1FfInner<'a> = (Uint1Ff, &'a [u8]);
impl View for Opaque1Ff<'_> {
    type V = SpecOpaque1Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ff<'a>> for Opaque1FfInner<'a> {
    fn ex_from(m: Opaque1Ff<'a>) -> Opaque1FfInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfInner<'a>> for Opaque1Ff<'a> {
    fn ex_from(m: Opaque1FfInner<'a>) -> Opaque1Ff<'a> {
        let (l, data) = m;
        Opaque1Ff {
            l,
            data,
        }
    }
}
pub struct Opaque1FfMapper;
impl View for Opaque1FfMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfMapper {
    type Src = SpecOpaque1FfInner;
    type Dst = SpecOpaque1Ff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque1FfMapper {
    type Src<'a> = Opaque1FfInner<'a>;
    type Dst<'a> = Opaque1Ff<'a>;
    type SrcOwned = Opaque1FfOwnedInner;
    type DstOwned = Opaque1FfOwned;
}
pub struct Opaque1FfOwned {
    pub l: Uint1FfOwned,
    pub data: Vec<u8>,
}
pub type Opaque1FfOwnedInner = (Uint1FfOwned, Vec<u8>);
impl View for Opaque1FfOwned {
    type V = SpecOpaque1Ff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque1FfOwned> for Opaque1FfOwnedInner {
    fn ex_from(m: Opaque1FfOwned) -> Opaque1FfOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque1FfOwnedInner> for Opaque1FfOwned {
    fn ex_from(m: Opaque1FfOwnedInner) -> Opaque1FfOwned {
        let (l, data) = m;
        Opaque1FfOwned {
            l,
            data,
        }
    }
}

pub type SpecProtocolName = SpecOpaque1Ff;
pub type ProtocolName<'a> = Opaque1Ff<'a>;
pub type ProtocolNameOwned = Opaque1FfOwned;

pub type SpecProtocolNameListList = Seq<SpecProtocolName>;
pub type ProtocolNameListList<'a> = RepeatResult<ProtocolName<'a>>;
pub type ProtocolNameListListOwned = RepeatResult<ProtocolNameOwned>;

pub struct SpecProtocolNameList {
    pub l: SpecUint2Ffff,
    pub list: SpecProtocolNameListList,
}
pub type SpecProtocolNameListInner = (SpecUint2Ffff, SpecProtocolNameListList);
impl SpecFrom<SpecProtocolNameList> for SpecProtocolNameListInner {
    open spec fn spec_from(m: SpecProtocolNameList) -> SpecProtocolNameListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecProtocolNameListInner> for SpecProtocolNameList {
    open spec fn spec_from(m: SpecProtocolNameListInner) -> SpecProtocolNameList {
        let (l, list) = m;
        SpecProtocolNameList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProtocolNameList<'a> {
    pub l: Uint2Ffff,
    pub list: ProtocolNameListList<'a>,
}
pub type ProtocolNameListInner<'a> = (Uint2Ffff, ProtocolNameListList<'a>);
impl View for ProtocolNameList<'_> {
    type V = SpecProtocolNameList;
    open spec fn view(&self) -> Self::V {
        SpecProtocolNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<ProtocolNameList<'a>> for ProtocolNameListInner<'a> {
    fn ex_from(m: ProtocolNameList<'a>) -> ProtocolNameListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<ProtocolNameListInner<'a>> for ProtocolNameList<'a> {
    fn ex_from(m: ProtocolNameListInner<'a>) -> ProtocolNameList<'a> {
        let (l, list) = m;
        ProtocolNameList {
            l,
            list,
        }
    }
}
pub struct ProtocolNameListMapper;
impl View for ProtocolNameListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ProtocolNameListMapper {
    type Src = SpecProtocolNameListInner;
    type Dst = SpecProtocolNameList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ProtocolNameListMapper {
    type Src<'a> = ProtocolNameListInner<'a>;
    type Dst<'a> = ProtocolNameList<'a>;
    type SrcOwned = ProtocolNameListOwnedInner;
    type DstOwned = ProtocolNameListOwned;
}
pub struct ProtocolNameListOwned {
    pub l: Uint2FfffOwned,
    pub list: ProtocolNameListListOwned,
}
pub type ProtocolNameListOwnedInner = (Uint2FfffOwned, ProtocolNameListListOwned);
impl View for ProtocolNameListOwned {
    type V = SpecProtocolNameList;
    open spec fn view(&self) -> Self::V {
        SpecProtocolNameList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<ProtocolNameListOwned> for ProtocolNameListOwnedInner {
    fn ex_from(m: ProtocolNameListOwned) -> ProtocolNameListOwnedInner {
        (m.l, m.list)
    }
}
impl From<ProtocolNameListOwnedInner> for ProtocolNameListOwned {
    fn ex_from(m: ProtocolNameListOwnedInner) -> ProtocolNameListOwned {
        let (l, list) = m;
        ProtocolNameListOwned {
            l,
            list,
        }
    }
}

pub type SpecSerializedSct = SpecOpaque1Ffff;
pub type SerializedSct<'a> = Opaque1Ffff<'a>;
pub type SerializedSctOwned = Opaque1FfffOwned;

pub type SpecSignedCertificateTimestampListList = Seq<SpecSerializedSct>;
pub type SignedCertificateTimestampListList<'a> = RepeatResult<SerializedSct<'a>>;
pub type SignedCertificateTimestampListListOwned = RepeatResult<SerializedSctOwned>;

pub struct SpecSignedCertificateTimestampList {
    pub l: SpecUint1Ffff,
    pub list: SpecSignedCertificateTimestampListList,
}
pub type SpecSignedCertificateTimestampListInner = (SpecUint1Ffff, SpecSignedCertificateTimestampListList);
impl SpecFrom<SpecSignedCertificateTimestampList> for SpecSignedCertificateTimestampListInner {
    open spec fn spec_from(m: SpecSignedCertificateTimestampList) -> SpecSignedCertificateTimestampListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecSignedCertificateTimestampListInner> for SpecSignedCertificateTimestampList {
    open spec fn spec_from(m: SpecSignedCertificateTimestampListInner) -> SpecSignedCertificateTimestampList {
        let (l, list) = m;
        SpecSignedCertificateTimestampList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedCertificateTimestampList<'a> {
    pub l: Uint1Ffff,
    pub list: SignedCertificateTimestampListList<'a>,
}
pub type SignedCertificateTimestampListInner<'a> = (Uint1Ffff, SignedCertificateTimestampListList<'a>);
impl View for SignedCertificateTimestampList<'_> {
    type V = SpecSignedCertificateTimestampList;
    open spec fn view(&self) -> Self::V {
        SpecSignedCertificateTimestampList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<SignedCertificateTimestampList<'a>> for SignedCertificateTimestampListInner<'a> {
    fn ex_from(m: SignedCertificateTimestampList<'a>) -> SignedCertificateTimestampListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<SignedCertificateTimestampListInner<'a>> for SignedCertificateTimestampList<'a> {
    fn ex_from(m: SignedCertificateTimestampListInner<'a>) -> SignedCertificateTimestampList<'a> {
        let (l, list) = m;
        SignedCertificateTimestampList {
            l,
            list,
        }
    }
}
pub struct SignedCertificateTimestampListMapper;
impl View for SignedCertificateTimestampListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SignedCertificateTimestampListMapper {
    type Src = SpecSignedCertificateTimestampListInner;
    type Dst = SpecSignedCertificateTimestampList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SignedCertificateTimestampListMapper {
    type Src<'a> = SignedCertificateTimestampListInner<'a>;
    type Dst<'a> = SignedCertificateTimestampList<'a>;
    type SrcOwned = SignedCertificateTimestampListOwnedInner;
    type DstOwned = SignedCertificateTimestampListOwned;
}
pub struct SignedCertificateTimestampListOwned {
    pub l: Uint1FfffOwned,
    pub list: SignedCertificateTimestampListListOwned,
}
pub type SignedCertificateTimestampListOwnedInner = (Uint1FfffOwned, SignedCertificateTimestampListListOwned);
impl View for SignedCertificateTimestampListOwned {
    type V = SpecSignedCertificateTimestampList;
    open spec fn view(&self) -> Self::V {
        SpecSignedCertificateTimestampList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<SignedCertificateTimestampListOwned> for SignedCertificateTimestampListOwnedInner {
    fn ex_from(m: SignedCertificateTimestampListOwned) -> SignedCertificateTimestampListOwnedInner {
        (m.l, m.list)
    }
}
impl From<SignedCertificateTimestampListOwnedInner> for SignedCertificateTimestampListOwned {
    fn ex_from(m: SignedCertificateTimestampListOwnedInner) -> SignedCertificateTimestampListOwned {
        let (l, list) = m;
        SignedCertificateTimestampListOwned {
            l,
            list,
        }
    }
}

pub type SpecCertificateType = u8;
pub type CertificateType = u8;
pub type CertificateTypeOwned = u8;

pub type SpecClientCertTypeClientExtensionTypes = Seq<SpecCertificateType>;
pub type ClientCertTypeClientExtensionTypes = RepeatResult<CertificateType>;
pub type ClientCertTypeClientExtensionTypesOwned = RepeatResult<CertificateTypeOwned>;

pub struct SpecClientCertTypeClientExtension {
    pub l: SpecUint1Ff,
    pub types: SpecClientCertTypeClientExtensionTypes,
}
pub type SpecClientCertTypeClientExtensionInner = (SpecUint1Ff, SpecClientCertTypeClientExtensionTypes);
impl SpecFrom<SpecClientCertTypeClientExtension> for SpecClientCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecClientCertTypeClientExtension) -> SpecClientCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl SpecFrom<SpecClientCertTypeClientExtensionInner> for SpecClientCertTypeClientExtension {
    open spec fn spec_from(m: SpecClientCertTypeClientExtensionInner) -> SpecClientCertTypeClientExtension {
        let (l, types) = m;
        SpecClientCertTypeClientExtension {
            l,
            types,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ClientCertTypeClientExtensionTypes,
}
pub type ClientCertTypeClientExtensionInner = (Uint1Ff, ClientCertTypeClientExtensionTypes);
impl View for ClientCertTypeClientExtension {
    type V = SpecClientCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ClientCertTypeClientExtension> for ClientCertTypeClientExtensionInner {
    fn ex_from(m: ClientCertTypeClientExtension) -> ClientCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ClientCertTypeClientExtensionInner> for ClientCertTypeClientExtension {
    fn ex_from(m: ClientCertTypeClientExtensionInner) -> ClientCertTypeClientExtension {
        let (l, types) = m;
        ClientCertTypeClientExtension {
            l,
            types,
        }
    }
}
pub struct ClientCertTypeClientExtensionMapper;
impl View for ClientCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeClientExtensionMapper {
    type Src = SpecClientCertTypeClientExtensionInner;
    type Dst = SpecClientCertTypeClientExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientCertTypeClientExtensionMapper {
    type Src<'a> = ClientCertTypeClientExtensionInner;
    type Dst<'a> = ClientCertTypeClientExtension;
    type SrcOwned = ClientCertTypeClientExtensionOwnedInner;
    type DstOwned = ClientCertTypeClientExtensionOwned;
}
pub struct ClientCertTypeClientExtensionOwned {
    pub l: Uint1FfOwned,
    pub types: ClientCertTypeClientExtensionTypesOwned,
}
pub type ClientCertTypeClientExtensionOwnedInner = (Uint1FfOwned, ClientCertTypeClientExtensionTypesOwned);
impl View for ClientCertTypeClientExtensionOwned {
    type V = SpecClientCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ClientCertTypeClientExtensionOwned> for ClientCertTypeClientExtensionOwnedInner {
    fn ex_from(m: ClientCertTypeClientExtensionOwned) -> ClientCertTypeClientExtensionOwnedInner {
        (m.l, m.types)
    }
}
impl From<ClientCertTypeClientExtensionOwnedInner> for ClientCertTypeClientExtensionOwned {
    fn ex_from(m: ClientCertTypeClientExtensionOwnedInner) -> ClientCertTypeClientExtensionOwned {
        let (l, types) = m;
        ClientCertTypeClientExtensionOwned {
            l,
            types,
        }
    }
}

pub type SpecServerCertTypeClientExtensionTypes = Seq<SpecCertificateType>;
pub type ServerCertTypeClientExtensionTypes = RepeatResult<CertificateType>;
pub type ServerCertTypeClientExtensionTypesOwned = RepeatResult<CertificateTypeOwned>;

pub struct SpecServerCertTypeClientExtension {
    pub l: SpecUint1Ff,
    pub types: SpecServerCertTypeClientExtensionTypes,
}
pub type SpecServerCertTypeClientExtensionInner = (SpecUint1Ff, SpecServerCertTypeClientExtensionTypes);
impl SpecFrom<SpecServerCertTypeClientExtension> for SpecServerCertTypeClientExtensionInner {
    open spec fn spec_from(m: SpecServerCertTypeClientExtension) -> SpecServerCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl SpecFrom<SpecServerCertTypeClientExtensionInner> for SpecServerCertTypeClientExtension {
    open spec fn spec_from(m: SpecServerCertTypeClientExtensionInner) -> SpecServerCertTypeClientExtension {
        let (l, types) = m;
        SpecServerCertTypeClientExtension {
            l,
            types,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerCertTypeClientExtension {
    pub l: Uint1Ff,
    pub types: ServerCertTypeClientExtensionTypes,
}
pub type ServerCertTypeClientExtensionInner = (Uint1Ff, ServerCertTypeClientExtensionTypes);
impl View for ServerCertTypeClientExtension {
    type V = SpecServerCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ServerCertTypeClientExtension> for ServerCertTypeClientExtensionInner {
    fn ex_from(m: ServerCertTypeClientExtension) -> ServerCertTypeClientExtensionInner {
        (m.l, m.types)
    }
}
impl From<ServerCertTypeClientExtensionInner> for ServerCertTypeClientExtension {
    fn ex_from(m: ServerCertTypeClientExtensionInner) -> ServerCertTypeClientExtension {
        let (l, types) = m;
        ServerCertTypeClientExtension {
            l,
            types,
        }
    }
}
pub struct ServerCertTypeClientExtensionMapper;
impl View for ServerCertTypeClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeClientExtensionMapper {
    type Src = SpecServerCertTypeClientExtensionInner;
    type Dst = SpecServerCertTypeClientExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerCertTypeClientExtensionMapper {
    type Src<'a> = ServerCertTypeClientExtensionInner;
    type Dst<'a> = ServerCertTypeClientExtension;
    type SrcOwned = ServerCertTypeClientExtensionOwnedInner;
    type DstOwned = ServerCertTypeClientExtensionOwned;
}
pub struct ServerCertTypeClientExtensionOwned {
    pub l: Uint1FfOwned,
    pub types: ServerCertTypeClientExtensionTypesOwned,
}
pub type ServerCertTypeClientExtensionOwnedInner = (Uint1FfOwned, ServerCertTypeClientExtensionTypesOwned);
impl View for ServerCertTypeClientExtensionOwned {
    type V = SpecServerCertTypeClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeClientExtension {
            l: self.l@,
            types: self.types@,
        }
    }
}
impl From<ServerCertTypeClientExtensionOwned> for ServerCertTypeClientExtensionOwnedInner {
    fn ex_from(m: ServerCertTypeClientExtensionOwned) -> ServerCertTypeClientExtensionOwnedInner {
        (m.l, m.types)
    }
}
impl From<ServerCertTypeClientExtensionOwnedInner> for ServerCertTypeClientExtensionOwned {
    fn ex_from(m: ServerCertTypeClientExtensionOwnedInner) -> ServerCertTypeClientExtensionOwned {
        let (l, types) = m;
        ServerCertTypeClientExtensionOwned {
            l,
            types,
        }
    }
}

pub struct SpecPaddingExtension {
    pub l: SpecUint0Ffff,
    pub padding: SpecPaddingExtensionPadding,
}
pub type SpecPaddingExtensionInner = (SpecUint0Ffff, SpecPaddingExtensionPadding);
impl SpecFrom<SpecPaddingExtension> for SpecPaddingExtensionInner {
    open spec fn spec_from(m: SpecPaddingExtension) -> SpecPaddingExtensionInner {
        (m.l, m.padding)
    }
}
impl SpecFrom<SpecPaddingExtensionInner> for SpecPaddingExtension {
    open spec fn spec_from(m: SpecPaddingExtensionInner) -> SpecPaddingExtension {
        let (l, padding) = m;
        SpecPaddingExtension {
            l,
            padding,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PaddingExtension {
    pub l: Uint0Ffff,
    pub padding: PaddingExtensionPadding,
}
pub type PaddingExtensionInner = (Uint0Ffff, PaddingExtensionPadding);
impl View for PaddingExtension {
    type V = SpecPaddingExtension;
    open spec fn view(&self) -> Self::V {
        SpecPaddingExtension {
            l: self.l@,
            padding: self.padding@,
        }
    }
}
impl From<PaddingExtension> for PaddingExtensionInner {
    fn ex_from(m: PaddingExtension) -> PaddingExtensionInner {
        (m.l, m.padding)
    }
}
impl From<PaddingExtensionInner> for PaddingExtension {
    fn ex_from(m: PaddingExtensionInner) -> PaddingExtension {
        let (l, padding) = m;
        PaddingExtension {
            l,
            padding,
        }
    }
}
pub struct PaddingExtensionMapper;
impl View for PaddingExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PaddingExtensionMapper {
    type Src = SpecPaddingExtensionInner;
    type Dst = SpecPaddingExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PaddingExtensionMapper {
    type Src<'a> = PaddingExtensionInner;
    type Dst<'a> = PaddingExtension;
    type SrcOwned = PaddingExtensionOwnedInner;
    type DstOwned = PaddingExtensionOwned;
}
pub struct PaddingExtensionOwned {
    pub l: Uint0FfffOwned,
    pub padding: PaddingExtensionPaddingOwned,
}
pub type PaddingExtensionOwnedInner = (Uint0FfffOwned, PaddingExtensionPaddingOwned);
impl View for PaddingExtensionOwned {
    type V = SpecPaddingExtension;
    open spec fn view(&self) -> Self::V {
        SpecPaddingExtension {
            l: self.l@,
            padding: self.padding@,
        }
    }
}
impl From<PaddingExtensionOwned> for PaddingExtensionOwnedInner {
    fn ex_from(m: PaddingExtensionOwned) -> PaddingExtensionOwnedInner {
        (m.l, m.padding)
    }
}
impl From<PaddingExtensionOwnedInner> for PaddingExtensionOwned {
    fn ex_from(m: PaddingExtensionOwnedInner) -> PaddingExtensionOwned {
        let (l, padding) = m;
        PaddingExtensionOwned {
            l,
            padding,
        }
    }
}

pub type SpecEmpty = Seq<u8>;
pub type Empty<'a> = &'a [u8];
pub type EmptyOwned = Vec<u8>;

pub struct SpecPskIdentity {
    pub identity: SpecOpaque1Ffff,
    pub obfuscated_ticket_age: u32,
}
pub type SpecPskIdentityInner = (SpecOpaque1Ffff, u32);
impl SpecFrom<SpecPskIdentity> for SpecPskIdentityInner {
    open spec fn spec_from(m: SpecPskIdentity) -> SpecPskIdentityInner {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl SpecFrom<SpecPskIdentityInner> for SpecPskIdentity {
    open spec fn spec_from(m: SpecPskIdentityInner) -> SpecPskIdentity {
        let (identity, obfuscated_ticket_age) = m;
        SpecPskIdentity {
            identity,
            obfuscated_ticket_age,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskIdentity<'a> {
    pub identity: Opaque1Ffff<'a>,
    pub obfuscated_ticket_age: u32,
}
pub type PskIdentityInner<'a> = (Opaque1Ffff<'a>, u32);
impl View for PskIdentity<'_> {
    type V = SpecPskIdentity;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentity {
            identity: self.identity@,
            obfuscated_ticket_age: self.obfuscated_ticket_age@,
        }
    }
}
impl<'a> From<PskIdentity<'a>> for PskIdentityInner<'a> {
    fn ex_from(m: PskIdentity<'a>) -> PskIdentityInner<'a> {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl<'a> From<PskIdentityInner<'a>> for PskIdentity<'a> {
    fn ex_from(m: PskIdentityInner<'a>) -> PskIdentity<'a> {
        let (identity, obfuscated_ticket_age) = m;
        PskIdentity {
            identity,
            obfuscated_ticket_age,
        }
    }
}
pub struct PskIdentityMapper;
impl View for PskIdentityMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentityMapper {
    type Src = SpecPskIdentityInner;
    type Dst = SpecPskIdentity;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PskIdentityMapper {
    type Src<'a> = PskIdentityInner<'a>;
    type Dst<'a> = PskIdentity<'a>;
    type SrcOwned = PskIdentityOwnedInner;
    type DstOwned = PskIdentityOwned;
}
pub struct PskIdentityOwned {
    pub identity: Opaque1FfffOwned,
    pub obfuscated_ticket_age: u32,
}
pub type PskIdentityOwnedInner = (Opaque1FfffOwned, u32);
impl View for PskIdentityOwned {
    type V = SpecPskIdentity;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentity {
            identity: self.identity@,
            obfuscated_ticket_age: self.obfuscated_ticket_age@,
        }
    }
}
impl From<PskIdentityOwned> for PskIdentityOwnedInner {
    fn ex_from(m: PskIdentityOwned) -> PskIdentityOwnedInner {
        (m.identity, m.obfuscated_ticket_age)
    }
}
impl From<PskIdentityOwnedInner> for PskIdentityOwned {
    fn ex_from(m: PskIdentityOwnedInner) -> PskIdentityOwned {
        let (identity, obfuscated_ticket_age) = m;
        PskIdentityOwned {
            identity,
            obfuscated_ticket_age,
        }
    }
}

pub type SpecPskIdentitiesIdentities = Seq<SpecPskIdentity>;
pub type PskIdentitiesIdentities<'a> = RepeatResult<PskIdentity<'a>>;
pub type PskIdentitiesIdentitiesOwned = RepeatResult<PskIdentityOwned>;

pub struct SpecPskIdentities {
    pub l: u16,
    pub identities: SpecPskIdentitiesIdentities,
}
pub type SpecPskIdentitiesInner = (u16, SpecPskIdentitiesIdentities);
impl SpecFrom<SpecPskIdentities> for SpecPskIdentitiesInner {
    open spec fn spec_from(m: SpecPskIdentities) -> SpecPskIdentitiesInner {
        (m.l, m.identities)
    }
}
impl SpecFrom<SpecPskIdentitiesInner> for SpecPskIdentities {
    open spec fn spec_from(m: SpecPskIdentitiesInner) -> SpecPskIdentities {
        let (l, identities) = m;
        SpecPskIdentities {
            l,
            identities,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskIdentities<'a> {
    pub l: u16,
    pub identities: PskIdentitiesIdentities<'a>,
}
pub type PskIdentitiesInner<'a> = (u16, PskIdentitiesIdentities<'a>);
impl View for PskIdentities<'_> {
    type V = SpecPskIdentities;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentities {
            l: self.l@,
            identities: self.identities@,
        }
    }
}
impl<'a> From<PskIdentities<'a>> for PskIdentitiesInner<'a> {
    fn ex_from(m: PskIdentities<'a>) -> PskIdentitiesInner<'a> {
        (m.l, m.identities)
    }
}
impl<'a> From<PskIdentitiesInner<'a>> for PskIdentities<'a> {
    fn ex_from(m: PskIdentitiesInner<'a>) -> PskIdentities<'a> {
        let (l, identities) = m;
        PskIdentities {
            l,
            identities,
        }
    }
}
pub struct PskIdentitiesMapper;
impl View for PskIdentitiesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskIdentitiesMapper {
    type Src = SpecPskIdentitiesInner;
    type Dst = SpecPskIdentities;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PskIdentitiesMapper {
    type Src<'a> = PskIdentitiesInner<'a>;
    type Dst<'a> = PskIdentities<'a>;
    type SrcOwned = PskIdentitiesOwnedInner;
    type DstOwned = PskIdentitiesOwned;
}
pub struct PskIdentitiesOwned {
    pub l: u16,
    pub identities: PskIdentitiesIdentitiesOwned,
}
pub type PskIdentitiesOwnedInner = (u16, PskIdentitiesIdentitiesOwned);
impl View for PskIdentitiesOwned {
    type V = SpecPskIdentities;
    open spec fn view(&self) -> Self::V {
        SpecPskIdentities {
            l: self.l@,
            identities: self.identities@,
        }
    }
}
impl From<PskIdentitiesOwned> for PskIdentitiesOwnedInner {
    fn ex_from(m: PskIdentitiesOwned) -> PskIdentitiesOwnedInner {
        (m.l, m.identities)
    }
}
impl From<PskIdentitiesOwnedInner> for PskIdentitiesOwned {
    fn ex_from(m: PskIdentitiesOwnedInner) -> PskIdentitiesOwned {
        let (l, identities) = m;
        PskIdentitiesOwned {
            l,
            identities,
        }
    }
}

pub struct SpecPskBinderEntry {
    pub l: u8,
    pub entries: Seq<u8>,
}
pub type SpecPskBinderEntryInner = (u8, Seq<u8>);
impl SpecFrom<SpecPskBinderEntry> for SpecPskBinderEntryInner {
    open spec fn spec_from(m: SpecPskBinderEntry) -> SpecPskBinderEntryInner {
        (m.l, m.entries)
    }
}
impl SpecFrom<SpecPskBinderEntryInner> for SpecPskBinderEntry {
    open spec fn spec_from(m: SpecPskBinderEntryInner) -> SpecPskBinderEntry {
        let (l, entries) = m;
        SpecPskBinderEntry {
            l,
            entries,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskBinderEntry<'a> {
    pub l: u8,
    pub entries: &'a [u8],
}
pub type PskBinderEntryInner<'a> = (u8, &'a [u8]);
impl View for PskBinderEntry<'_> {
    type V = SpecPskBinderEntry;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntry {
            l: self.l@,
            entries: self.entries@,
        }
    }
}
impl<'a> From<PskBinderEntry<'a>> for PskBinderEntryInner<'a> {
    fn ex_from(m: PskBinderEntry<'a>) -> PskBinderEntryInner<'a> {
        (m.l, m.entries)
    }
}
impl<'a> From<PskBinderEntryInner<'a>> for PskBinderEntry<'a> {
    fn ex_from(m: PskBinderEntryInner<'a>) -> PskBinderEntry<'a> {
        let (l, entries) = m;
        PskBinderEntry {
            l,
            entries,
        }
    }
}
pub struct PskBinderEntryMapper;
impl View for PskBinderEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntryMapper {
    type Src = SpecPskBinderEntryInner;
    type Dst = SpecPskBinderEntry;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PskBinderEntryMapper {
    type Src<'a> = PskBinderEntryInner<'a>;
    type Dst<'a> = PskBinderEntry<'a>;
    type SrcOwned = PskBinderEntryOwnedInner;
    type DstOwned = PskBinderEntryOwned;
}
pub struct PskBinderEntryOwned {
    pub l: u8,
    pub entries: Vec<u8>,
}
pub type PskBinderEntryOwnedInner = (u8, Vec<u8>);
impl View for PskBinderEntryOwned {
    type V = SpecPskBinderEntry;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntry {
            l: self.l@,
            entries: self.entries@,
        }
    }
}
impl From<PskBinderEntryOwned> for PskBinderEntryOwnedInner {
    fn ex_from(m: PskBinderEntryOwned) -> PskBinderEntryOwnedInner {
        (m.l, m.entries)
    }
}
impl From<PskBinderEntryOwnedInner> for PskBinderEntryOwned {
    fn ex_from(m: PskBinderEntryOwnedInner) -> PskBinderEntryOwned {
        let (l, entries) = m;
        PskBinderEntryOwned {
            l,
            entries,
        }
    }
}

pub type SpecPskBinderEntriesBinders = Seq<SpecPskBinderEntry>;
pub type PskBinderEntriesBinders<'a> = RepeatResult<PskBinderEntry<'a>>;
pub type PskBinderEntriesBindersOwned = RepeatResult<PskBinderEntryOwned>;

pub struct SpecPskBinderEntries {
    pub l: u16,
    pub binders: SpecPskBinderEntriesBinders,
}
pub type SpecPskBinderEntriesInner = (u16, SpecPskBinderEntriesBinders);
impl SpecFrom<SpecPskBinderEntries> for SpecPskBinderEntriesInner {
    open spec fn spec_from(m: SpecPskBinderEntries) -> SpecPskBinderEntriesInner {
        (m.l, m.binders)
    }
}
impl SpecFrom<SpecPskBinderEntriesInner> for SpecPskBinderEntries {
    open spec fn spec_from(m: SpecPskBinderEntriesInner) -> SpecPskBinderEntries {
        let (l, binders) = m;
        SpecPskBinderEntries {
            l,
            binders,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskBinderEntries<'a> {
    pub l: u16,
    pub binders: PskBinderEntriesBinders<'a>,
}
pub type PskBinderEntriesInner<'a> = (u16, PskBinderEntriesBinders<'a>);
impl View for PskBinderEntries<'_> {
    type V = SpecPskBinderEntries;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntries {
            l: self.l@,
            binders: self.binders@,
        }
    }
}
impl<'a> From<PskBinderEntries<'a>> for PskBinderEntriesInner<'a> {
    fn ex_from(m: PskBinderEntries<'a>) -> PskBinderEntriesInner<'a> {
        (m.l, m.binders)
    }
}
impl<'a> From<PskBinderEntriesInner<'a>> for PskBinderEntries<'a> {
    fn ex_from(m: PskBinderEntriesInner<'a>) -> PskBinderEntries<'a> {
        let (l, binders) = m;
        PskBinderEntries {
            l,
            binders,
        }
    }
}
pub struct PskBinderEntriesMapper;
impl View for PskBinderEntriesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskBinderEntriesMapper {
    type Src = SpecPskBinderEntriesInner;
    type Dst = SpecPskBinderEntries;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PskBinderEntriesMapper {
    type Src<'a> = PskBinderEntriesInner<'a>;
    type Dst<'a> = PskBinderEntries<'a>;
    type SrcOwned = PskBinderEntriesOwnedInner;
    type DstOwned = PskBinderEntriesOwned;
}
pub struct PskBinderEntriesOwned {
    pub l: u16,
    pub binders: PskBinderEntriesBindersOwned,
}
pub type PskBinderEntriesOwnedInner = (u16, PskBinderEntriesBindersOwned);
impl View for PskBinderEntriesOwned {
    type V = SpecPskBinderEntries;
    open spec fn view(&self) -> Self::V {
        SpecPskBinderEntries {
            l: self.l@,
            binders: self.binders@,
        }
    }
}
impl From<PskBinderEntriesOwned> for PskBinderEntriesOwnedInner {
    fn ex_from(m: PskBinderEntriesOwned) -> PskBinderEntriesOwnedInner {
        (m.l, m.binders)
    }
}
impl From<PskBinderEntriesOwnedInner> for PskBinderEntriesOwned {
    fn ex_from(m: PskBinderEntriesOwnedInner) -> PskBinderEntriesOwned {
        let (l, binders) = m;
        PskBinderEntriesOwned {
            l,
            binders,
        }
    }
}

pub struct SpecOfferedPsks {
    pub identities: SpecPskIdentities,
    pub binders: SpecPskBinderEntries,
}
pub type SpecOfferedPsksInner = (SpecPskIdentities, SpecPskBinderEntries);
impl SpecFrom<SpecOfferedPsks> for SpecOfferedPsksInner {
    open spec fn spec_from(m: SpecOfferedPsks) -> SpecOfferedPsksInner {
        (m.identities, m.binders)
    }
}
impl SpecFrom<SpecOfferedPsksInner> for SpecOfferedPsks {
    open spec fn spec_from(m: SpecOfferedPsksInner) -> SpecOfferedPsks {
        let (identities, binders) = m;
        SpecOfferedPsks {
            identities,
            binders,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OfferedPsks<'a> {
    pub identities: PskIdentities<'a>,
    pub binders: PskBinderEntries<'a>,
}
pub type OfferedPsksInner<'a> = (PskIdentities<'a>, PskBinderEntries<'a>);
impl View for OfferedPsks<'_> {
    type V = SpecOfferedPsks;
    open spec fn view(&self) -> Self::V {
        SpecOfferedPsks {
            identities: self.identities@,
            binders: self.binders@,
        }
    }
}
impl<'a> From<OfferedPsks<'a>> for OfferedPsksInner<'a> {
    fn ex_from(m: OfferedPsks<'a>) -> OfferedPsksInner<'a> {
        (m.identities, m.binders)
    }
}
impl<'a> From<OfferedPsksInner<'a>> for OfferedPsks<'a> {
    fn ex_from(m: OfferedPsksInner<'a>) -> OfferedPsks<'a> {
        let (identities, binders) = m;
        OfferedPsks {
            identities,
            binders,
        }
    }
}
pub struct OfferedPsksMapper;
impl View for OfferedPsksMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OfferedPsksMapper {
    type Src = SpecOfferedPsksInner;
    type Dst = SpecOfferedPsks;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for OfferedPsksMapper {
    type Src<'a> = OfferedPsksInner<'a>;
    type Dst<'a> = OfferedPsks<'a>;
    type SrcOwned = OfferedPsksOwnedInner;
    type DstOwned = OfferedPsksOwned;
}
pub struct OfferedPsksOwned {
    pub identities: PskIdentitiesOwned,
    pub binders: PskBinderEntriesOwned,
}
pub type OfferedPsksOwnedInner = (PskIdentitiesOwned, PskBinderEntriesOwned);
impl View for OfferedPsksOwned {
    type V = SpecOfferedPsks;
    open spec fn view(&self) -> Self::V {
        SpecOfferedPsks {
            identities: self.identities@,
            binders: self.binders@,
        }
    }
}
impl From<OfferedPsksOwned> for OfferedPsksOwnedInner {
    fn ex_from(m: OfferedPsksOwned) -> OfferedPsksOwnedInner {
        (m.identities, m.binders)
    }
}
impl From<OfferedPsksOwnedInner> for OfferedPsksOwned {
    fn ex_from(m: OfferedPsksOwnedInner) -> OfferedPsksOwned {
        let (identities, binders) = m;
        OfferedPsksOwned {
            identities,
            binders,
        }
    }
}

pub struct SpecPreSharedKeyClientExtension {
    pub offers: SpecOfferedPsks,
}
pub type SpecPreSharedKeyClientExtensionInner = SpecOfferedPsks;
impl SpecFrom<SpecPreSharedKeyClientExtension> for SpecPreSharedKeyClientExtensionInner {
    open spec fn spec_from(m: SpecPreSharedKeyClientExtension) -> SpecPreSharedKeyClientExtensionInner {
        m.offers
    }
}
impl SpecFrom<SpecPreSharedKeyClientExtensionInner> for SpecPreSharedKeyClientExtension {
    open spec fn spec_from(m: SpecPreSharedKeyClientExtensionInner) -> SpecPreSharedKeyClientExtension {
        let offers = m;
        SpecPreSharedKeyClientExtension {
            offers,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreSharedKeyClientExtension<'a> {
    pub offers: OfferedPsks<'a>,
}
pub type PreSharedKeyClientExtensionInner<'a> = OfferedPsks<'a>;
impl View for PreSharedKeyClientExtension<'_> {
    type V = SpecPreSharedKeyClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyClientExtension {
            offers: self.offers@,
        }
    }
}
impl<'a> From<PreSharedKeyClientExtension<'a>> for PreSharedKeyClientExtensionInner<'a> {
    fn ex_from(m: PreSharedKeyClientExtension<'a>) -> PreSharedKeyClientExtensionInner<'a> {
        m.offers
    }
}
impl<'a> From<PreSharedKeyClientExtensionInner<'a>> for PreSharedKeyClientExtension<'a> {
    fn ex_from(m: PreSharedKeyClientExtensionInner<'a>) -> PreSharedKeyClientExtension<'a> {
        let offers = m;
        PreSharedKeyClientExtension {
            offers,
        }
    }
}
pub struct PreSharedKeyClientExtensionMapper;
impl View for PreSharedKeyClientExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyClientExtensionMapper {
    type Src = SpecPreSharedKeyClientExtensionInner;
    type Dst = SpecPreSharedKeyClientExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PreSharedKeyClientExtensionMapper {
    type Src<'a> = PreSharedKeyClientExtensionInner<'a>;
    type Dst<'a> = PreSharedKeyClientExtension<'a>;
    type SrcOwned = PreSharedKeyClientExtensionOwnedInner;
    type DstOwned = PreSharedKeyClientExtensionOwned;
}
pub struct PreSharedKeyClientExtensionOwned {
    pub offers: OfferedPsksOwned,
}
pub type PreSharedKeyClientExtensionOwnedInner = OfferedPsksOwned;
impl View for PreSharedKeyClientExtensionOwned {
    type V = SpecPreSharedKeyClientExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyClientExtension {
            offers: self.offers@,
        }
    }
}
impl From<PreSharedKeyClientExtensionOwned> for PreSharedKeyClientExtensionOwnedInner {
    fn ex_from(m: PreSharedKeyClientExtensionOwned) -> PreSharedKeyClientExtensionOwnedInner {
        m.offers
    }
}
impl From<PreSharedKeyClientExtensionOwnedInner> for PreSharedKeyClientExtensionOwned {
    fn ex_from(m: PreSharedKeyClientExtensionOwnedInner) -> PreSharedKeyClientExtensionOwned {
        let offers = m;
        PreSharedKeyClientExtensionOwned {
            offers,
        }
    }
}

pub struct SpecSupportedVersionsClient {
    pub l: u8,
    pub versions: SpecSupportedVersionsClientVersions,
}
pub type SpecSupportedVersionsClientInner = (u8, SpecSupportedVersionsClientVersions);
impl SpecFrom<SpecSupportedVersionsClient> for SpecSupportedVersionsClientInner {
    open spec fn spec_from(m: SpecSupportedVersionsClient) -> SpecSupportedVersionsClientInner {
        (m.l, m.versions)
    }
}
impl SpecFrom<SpecSupportedVersionsClientInner> for SpecSupportedVersionsClient {
    open spec fn spec_from(m: SpecSupportedVersionsClientInner) -> SpecSupportedVersionsClient {
        let (l, versions) = m;
        SpecSupportedVersionsClient {
            l,
            versions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupportedVersionsClient {
    pub l: u8,
    pub versions: SupportedVersionsClientVersions,
}
pub type SupportedVersionsClientInner = (u8, SupportedVersionsClientVersions);
impl View for SupportedVersionsClient {
    type V = SpecSupportedVersionsClient;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsClient {
            l: self.l@,
            versions: self.versions@,
        }
    }
}
impl From<SupportedVersionsClient> for SupportedVersionsClientInner {
    fn ex_from(m: SupportedVersionsClient) -> SupportedVersionsClientInner {
        (m.l, m.versions)
    }
}
impl From<SupportedVersionsClientInner> for SupportedVersionsClient {
    fn ex_from(m: SupportedVersionsClientInner) -> SupportedVersionsClient {
        let (l, versions) = m;
        SupportedVersionsClient {
            l,
            versions,
        }
    }
}
pub struct SupportedVersionsClientMapper;
impl View for SupportedVersionsClientMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SupportedVersionsClientMapper {
    type Src = SpecSupportedVersionsClientInner;
    type Dst = SpecSupportedVersionsClient;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SupportedVersionsClientMapper {
    type Src<'a> = SupportedVersionsClientInner;
    type Dst<'a> = SupportedVersionsClient;
    type SrcOwned = SupportedVersionsClientOwnedInner;
    type DstOwned = SupportedVersionsClientOwned;
}
pub struct SupportedVersionsClientOwned {
    pub l: u8,
    pub versions: SupportedVersionsClientVersionsOwned,
}
pub type SupportedVersionsClientOwnedInner = (u8, SupportedVersionsClientVersionsOwned);
impl View for SupportedVersionsClientOwned {
    type V = SpecSupportedVersionsClient;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsClient {
            l: self.l@,
            versions: self.versions@,
        }
    }
}
impl From<SupportedVersionsClientOwned> for SupportedVersionsClientOwnedInner {
    fn ex_from(m: SupportedVersionsClientOwned) -> SupportedVersionsClientOwnedInner {
        (m.l, m.versions)
    }
}
impl From<SupportedVersionsClientOwnedInner> for SupportedVersionsClientOwned {
    fn ex_from(m: SupportedVersionsClientOwnedInner) -> SupportedVersionsClientOwned {
        let (l, versions) = m;
        SupportedVersionsClientOwned {
            l,
            versions,
        }
    }
}

pub type SpecCookie = SpecOpaque1Ffff;
pub type Cookie<'a> = Opaque1Ffff<'a>;
pub type CookieOwned = Opaque1FfffOwned;

pub struct SpecPskKeyExchangeModes {
    pub l: SpecUint1Ff,
    pub modes: SpecPskKeyExchangeModesModes,
}
pub type SpecPskKeyExchangeModesInner = (SpecUint1Ff, SpecPskKeyExchangeModesModes);
impl SpecFrom<SpecPskKeyExchangeModes> for SpecPskKeyExchangeModesInner {
    open spec fn spec_from(m: SpecPskKeyExchangeModes) -> SpecPskKeyExchangeModesInner {
        (m.l, m.modes)
    }
}
impl SpecFrom<SpecPskKeyExchangeModesInner> for SpecPskKeyExchangeModes {
    open spec fn spec_from(m: SpecPskKeyExchangeModesInner) -> SpecPskKeyExchangeModes {
        let (l, modes) = m;
        SpecPskKeyExchangeModes {
            l,
            modes,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PskKeyExchangeModes {
    pub l: Uint1Ff,
    pub modes: PskKeyExchangeModesModes,
}
pub type PskKeyExchangeModesInner = (Uint1Ff, PskKeyExchangeModesModes);
impl View for PskKeyExchangeModes {
    type V = SpecPskKeyExchangeModes;
    open spec fn view(&self) -> Self::V {
        SpecPskKeyExchangeModes {
            l: self.l@,
            modes: self.modes@,
        }
    }
}
impl From<PskKeyExchangeModes> for PskKeyExchangeModesInner {
    fn ex_from(m: PskKeyExchangeModes) -> PskKeyExchangeModesInner {
        (m.l, m.modes)
    }
}
impl From<PskKeyExchangeModesInner> for PskKeyExchangeModes {
    fn ex_from(m: PskKeyExchangeModesInner) -> PskKeyExchangeModes {
        let (l, modes) = m;
        PskKeyExchangeModes {
            l,
            modes,
        }
    }
}
pub struct PskKeyExchangeModesMapper;
impl View for PskKeyExchangeModesMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PskKeyExchangeModesMapper {
    type Src = SpecPskKeyExchangeModesInner;
    type Dst = SpecPskKeyExchangeModes;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PskKeyExchangeModesMapper {
    type Src<'a> = PskKeyExchangeModesInner;
    type Dst<'a> = PskKeyExchangeModes;
    type SrcOwned = PskKeyExchangeModesOwnedInner;
    type DstOwned = PskKeyExchangeModesOwned;
}
pub struct PskKeyExchangeModesOwned {
    pub l: Uint1FfOwned,
    pub modes: PskKeyExchangeModesModesOwned,
}
pub type PskKeyExchangeModesOwnedInner = (Uint1FfOwned, PskKeyExchangeModesModesOwned);
impl View for PskKeyExchangeModesOwned {
    type V = SpecPskKeyExchangeModes;
    open spec fn view(&self) -> Self::V {
        SpecPskKeyExchangeModes {
            l: self.l@,
            modes: self.modes@,
        }
    }
}
impl From<PskKeyExchangeModesOwned> for PskKeyExchangeModesOwnedInner {
    fn ex_from(m: PskKeyExchangeModesOwned) -> PskKeyExchangeModesOwnedInner {
        (m.l, m.modes)
    }
}
impl From<PskKeyExchangeModesOwnedInner> for PskKeyExchangeModesOwned {
    fn ex_from(m: PskKeyExchangeModesOwnedInner) -> PskKeyExchangeModesOwned {
        let (l, modes) = m;
        PskKeyExchangeModesOwned {
            l,
            modes,
        }
    }
}

pub type SpecDistinguishedName = SpecOpaque1Ffff;
pub type DistinguishedName<'a> = Opaque1Ffff<'a>;
pub type DistinguishedNameOwned = Opaque1FfffOwned;

pub type SpecCertificateAuthoritiesExtensionAuthorities = Seq<SpecDistinguishedName>;
pub type CertificateAuthoritiesExtensionAuthorities<'a> = RepeatResult<DistinguishedName<'a>>;
pub type CertificateAuthoritiesExtensionAuthoritiesOwned = RepeatResult<DistinguishedNameOwned>;

pub struct SpecCertificateAuthoritiesExtension {
    pub l: u16,
    pub authorities: SpecCertificateAuthoritiesExtensionAuthorities,
}
pub type SpecCertificateAuthoritiesExtensionInner = (u16, SpecCertificateAuthoritiesExtensionAuthorities);
impl SpecFrom<SpecCertificateAuthoritiesExtension> for SpecCertificateAuthoritiesExtensionInner {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtension) -> SpecCertificateAuthoritiesExtensionInner {
        (m.l, m.authorities)
    }
}
impl SpecFrom<SpecCertificateAuthoritiesExtensionInner> for SpecCertificateAuthoritiesExtension {
    open spec fn spec_from(m: SpecCertificateAuthoritiesExtensionInner) -> SpecCertificateAuthoritiesExtension {
        let (l, authorities) = m;
        SpecCertificateAuthoritiesExtension {
            l,
            authorities,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateAuthoritiesExtension<'a> {
    pub l: u16,
    pub authorities: CertificateAuthoritiesExtensionAuthorities<'a>,
}
pub type CertificateAuthoritiesExtensionInner<'a> = (u16, CertificateAuthoritiesExtensionAuthorities<'a>);
impl View for CertificateAuthoritiesExtension<'_> {
    type V = SpecCertificateAuthoritiesExtension;
    open spec fn view(&self) -> Self::V {
        SpecCertificateAuthoritiesExtension {
            l: self.l@,
            authorities: self.authorities@,
        }
    }
}
impl<'a> From<CertificateAuthoritiesExtension<'a>> for CertificateAuthoritiesExtensionInner<'a> {
    fn ex_from(m: CertificateAuthoritiesExtension<'a>) -> CertificateAuthoritiesExtensionInner<'a> {
        (m.l, m.authorities)
    }
}
impl<'a> From<CertificateAuthoritiesExtensionInner<'a>> for CertificateAuthoritiesExtension<'a> {
    fn ex_from(m: CertificateAuthoritiesExtensionInner<'a>) -> CertificateAuthoritiesExtension<'a> {
        let (l, authorities) = m;
        CertificateAuthoritiesExtension {
            l,
            authorities,
        }
    }
}
pub struct CertificateAuthoritiesExtensionMapper;
impl View for CertificateAuthoritiesExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateAuthoritiesExtensionMapper {
    type Src = SpecCertificateAuthoritiesExtensionInner;
    type Dst = SpecCertificateAuthoritiesExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateAuthoritiesExtensionMapper {
    type Src<'a> = CertificateAuthoritiesExtensionInner<'a>;
    type Dst<'a> = CertificateAuthoritiesExtension<'a>;
    type SrcOwned = CertificateAuthoritiesExtensionOwnedInner;
    type DstOwned = CertificateAuthoritiesExtensionOwned;
}
pub struct CertificateAuthoritiesExtensionOwned {
    pub l: u16,
    pub authorities: CertificateAuthoritiesExtensionAuthoritiesOwned,
}
pub type CertificateAuthoritiesExtensionOwnedInner = (u16, CertificateAuthoritiesExtensionAuthoritiesOwned);
impl View for CertificateAuthoritiesExtensionOwned {
    type V = SpecCertificateAuthoritiesExtension;
    open spec fn view(&self) -> Self::V {
        SpecCertificateAuthoritiesExtension {
            l: self.l@,
            authorities: self.authorities@,
        }
    }
}
impl From<CertificateAuthoritiesExtensionOwned> for CertificateAuthoritiesExtensionOwnedInner {
    fn ex_from(m: CertificateAuthoritiesExtensionOwned) -> CertificateAuthoritiesExtensionOwnedInner {
        (m.l, m.authorities)
    }
}
impl From<CertificateAuthoritiesExtensionOwnedInner> for CertificateAuthoritiesExtensionOwned {
    fn ex_from(m: CertificateAuthoritiesExtensionOwnedInner) -> CertificateAuthoritiesExtensionOwned {
        let (l, authorities) = m;
        CertificateAuthoritiesExtensionOwned {
            l,
            authorities,
        }
    }
}

pub struct SpecOidFilter {
    pub certificate_extension_oid: SpecOpaque1Ff,
    pub certificate_extension_values: SpecOpaque0Ffff,
}
pub type SpecOidFilterInner = (SpecOpaque1Ff, SpecOpaque0Ffff);
impl SpecFrom<SpecOidFilter> for SpecOidFilterInner {
    open spec fn spec_from(m: SpecOidFilter) -> SpecOidFilterInner {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl SpecFrom<SpecOidFilterInner> for SpecOidFilter {
    open spec fn spec_from(m: SpecOidFilterInner) -> SpecOidFilter {
        let (certificate_extension_oid, certificate_extension_values) = m;
        SpecOidFilter {
            certificate_extension_oid,
            certificate_extension_values,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OidFilter<'a> {
    pub certificate_extension_oid: Opaque1Ff<'a>,
    pub certificate_extension_values: Opaque0Ffff<'a>,
}
pub type OidFilterInner<'a> = (Opaque1Ff<'a>, Opaque0Ffff<'a>);
impl View for OidFilter<'_> {
    type V = SpecOidFilter;
    open spec fn view(&self) -> Self::V {
        SpecOidFilter {
            certificate_extension_oid: self.certificate_extension_oid@,
            certificate_extension_values: self.certificate_extension_values@,
        }
    }
}
impl<'a> From<OidFilter<'a>> for OidFilterInner<'a> {
    fn ex_from(m: OidFilter<'a>) -> OidFilterInner<'a> {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl<'a> From<OidFilterInner<'a>> for OidFilter<'a> {
    fn ex_from(m: OidFilterInner<'a>) -> OidFilter<'a> {
        let (certificate_extension_oid, certificate_extension_values) = m;
        OidFilter {
            certificate_extension_oid,
            certificate_extension_values,
        }
    }
}
pub struct OidFilterMapper;
impl View for OidFilterMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterMapper {
    type Src = SpecOidFilterInner;
    type Dst = SpecOidFilter;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for OidFilterMapper {
    type Src<'a> = OidFilterInner<'a>;
    type Dst<'a> = OidFilter<'a>;
    type SrcOwned = OidFilterOwnedInner;
    type DstOwned = OidFilterOwned;
}
pub struct OidFilterOwned {
    pub certificate_extension_oid: Opaque1FfOwned,
    pub certificate_extension_values: Opaque0FfffOwned,
}
pub type OidFilterOwnedInner = (Opaque1FfOwned, Opaque0FfffOwned);
impl View for OidFilterOwned {
    type V = SpecOidFilter;
    open spec fn view(&self) -> Self::V {
        SpecOidFilter {
            certificate_extension_oid: self.certificate_extension_oid@,
            certificate_extension_values: self.certificate_extension_values@,
        }
    }
}
impl From<OidFilterOwned> for OidFilterOwnedInner {
    fn ex_from(m: OidFilterOwned) -> OidFilterOwnedInner {
        (m.certificate_extension_oid, m.certificate_extension_values)
    }
}
impl From<OidFilterOwnedInner> for OidFilterOwned {
    fn ex_from(m: OidFilterOwnedInner) -> OidFilterOwned {
        let (certificate_extension_oid, certificate_extension_values) = m;
        OidFilterOwned {
            certificate_extension_oid,
            certificate_extension_values,
        }
    }
}

pub type SpecOidFilterExtensionFilters = Seq<SpecOidFilter>;
pub type OidFilterExtensionFilters<'a> = RepeatResult<OidFilter<'a>>;
pub type OidFilterExtensionFiltersOwned = RepeatResult<OidFilterOwned>;

pub struct SpecOidFilterExtension {
    pub l: SpecUint0Ffff,
    pub filters: SpecOidFilterExtensionFilters,
}
pub type SpecOidFilterExtensionInner = (SpecUint0Ffff, SpecOidFilterExtensionFilters);
impl SpecFrom<SpecOidFilterExtension> for SpecOidFilterExtensionInner {
    open spec fn spec_from(m: SpecOidFilterExtension) -> SpecOidFilterExtensionInner {
        (m.l, m.filters)
    }
}
impl SpecFrom<SpecOidFilterExtensionInner> for SpecOidFilterExtension {
    open spec fn spec_from(m: SpecOidFilterExtensionInner) -> SpecOidFilterExtension {
        let (l, filters) = m;
        SpecOidFilterExtension {
            l,
            filters,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OidFilterExtension<'a> {
    pub l: Uint0Ffff,
    pub filters: OidFilterExtensionFilters<'a>,
}
pub type OidFilterExtensionInner<'a> = (Uint0Ffff, OidFilterExtensionFilters<'a>);
impl View for OidFilterExtension<'_> {
    type V = SpecOidFilterExtension;
    open spec fn view(&self) -> Self::V {
        SpecOidFilterExtension {
            l: self.l@,
            filters: self.filters@,
        }
    }
}
impl<'a> From<OidFilterExtension<'a>> for OidFilterExtensionInner<'a> {
    fn ex_from(m: OidFilterExtension<'a>) -> OidFilterExtensionInner<'a> {
        (m.l, m.filters)
    }
}
impl<'a> From<OidFilterExtensionInner<'a>> for OidFilterExtension<'a> {
    fn ex_from(m: OidFilterExtensionInner<'a>) -> OidFilterExtension<'a> {
        let (l, filters) = m;
        OidFilterExtension {
            l,
            filters,
        }
    }
}
pub struct OidFilterExtensionMapper;
impl View for OidFilterExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for OidFilterExtensionMapper {
    type Src = SpecOidFilterExtensionInner;
    type Dst = SpecOidFilterExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for OidFilterExtensionMapper {
    type Src<'a> = OidFilterExtensionInner<'a>;
    type Dst<'a> = OidFilterExtension<'a>;
    type SrcOwned = OidFilterExtensionOwnedInner;
    type DstOwned = OidFilterExtensionOwned;
}
pub struct OidFilterExtensionOwned {
    pub l: Uint0FfffOwned,
    pub filters: OidFilterExtensionFiltersOwned,
}
pub type OidFilterExtensionOwnedInner = (Uint0FfffOwned, OidFilterExtensionFiltersOwned);
impl View for OidFilterExtensionOwned {
    type V = SpecOidFilterExtension;
    open spec fn view(&self) -> Self::V {
        SpecOidFilterExtension {
            l: self.l@,
            filters: self.filters@,
        }
    }
}
impl From<OidFilterExtensionOwned> for OidFilterExtensionOwnedInner {
    fn ex_from(m: OidFilterExtensionOwned) -> OidFilterExtensionOwnedInner {
        (m.l, m.filters)
    }
}
impl From<OidFilterExtensionOwnedInner> for OidFilterExtensionOwned {
    fn ex_from(m: OidFilterExtensionOwnedInner) -> OidFilterExtensionOwned {
        let (l, filters) = m;
        OidFilterExtensionOwned {
            l,
            filters,
        }
    }
}

pub struct SpecUncompressedPointRepresentation32 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}
pub type SpecUncompressedPointRepresentation32Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation32> for SpecUncompressedPointRepresentation32Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation32) -> SpecUncompressedPointRepresentation32Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation32Inner> for SpecUncompressedPointRepresentation32 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation32Inner) -> SpecUncompressedPointRepresentation32 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation32 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation32<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation32Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl View for UncompressedPointRepresentation32<'_> {
    type V = SpecUncompressedPointRepresentation32;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation32 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl<'a> From<UncompressedPointRepresentation32<'a>> for UncompressedPointRepresentation32Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation32<'a>) -> UncompressedPointRepresentation32Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation32Inner<'a>> for UncompressedPointRepresentation32<'a> {
    fn ex_from(m: UncompressedPointRepresentation32Inner<'a>) -> UncompressedPointRepresentation32<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation32 {
            legacy_form,
            x,
            y,
        }
    }
}
pub struct UncompressedPointRepresentation32Mapper;
impl View for UncompressedPointRepresentation32Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation32Mapper {
    type Src = SpecUncompressedPointRepresentation32Inner;
    type Dst = SpecUncompressedPointRepresentation32;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for UncompressedPointRepresentation32Mapper {
    type Src<'a> = UncompressedPointRepresentation32Inner<'a>;
    type Dst<'a> = UncompressedPointRepresentation32<'a>;
    type SrcOwned = UncompressedPointRepresentation32OwnedInner;
    type DstOwned = UncompressedPointRepresentation32Owned;
}
pub struct UncompressedPointRepresentation32Owned {
    pub legacy_form: u8,
    pub x: Vec<u8>,
    pub y: Vec<u8>,
}
pub type UncompressedPointRepresentation32OwnedInner = (u8, (Vec<u8>, Vec<u8>));
impl View for UncompressedPointRepresentation32Owned {
    type V = SpecUncompressedPointRepresentation32;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation32 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl From<UncompressedPointRepresentation32Owned> for UncompressedPointRepresentation32OwnedInner {
    fn ex_from(m: UncompressedPointRepresentation32Owned) -> UncompressedPointRepresentation32OwnedInner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl From<UncompressedPointRepresentation32OwnedInner> for UncompressedPointRepresentation32Owned {
    fn ex_from(m: UncompressedPointRepresentation32OwnedInner) -> UncompressedPointRepresentation32Owned {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation32Owned {
            legacy_form,
            x,
            y,
        }
    }
}

pub struct SpecUncompressedPointRepresentation48 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}
pub type SpecUncompressedPointRepresentation48Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation48> for SpecUncompressedPointRepresentation48Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation48) -> SpecUncompressedPointRepresentation48Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation48Inner> for SpecUncompressedPointRepresentation48 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation48Inner) -> SpecUncompressedPointRepresentation48 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation48 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation48<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation48Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl View for UncompressedPointRepresentation48<'_> {
    type V = SpecUncompressedPointRepresentation48;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation48 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl<'a> From<UncompressedPointRepresentation48<'a>> for UncompressedPointRepresentation48Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation48<'a>) -> UncompressedPointRepresentation48Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation48Inner<'a>> for UncompressedPointRepresentation48<'a> {
    fn ex_from(m: UncompressedPointRepresentation48Inner<'a>) -> UncompressedPointRepresentation48<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation48 {
            legacy_form,
            x,
            y,
        }
    }
}
pub struct UncompressedPointRepresentation48Mapper;
impl View for UncompressedPointRepresentation48Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation48Mapper {
    type Src = SpecUncompressedPointRepresentation48Inner;
    type Dst = SpecUncompressedPointRepresentation48;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for UncompressedPointRepresentation48Mapper {
    type Src<'a> = UncompressedPointRepresentation48Inner<'a>;
    type Dst<'a> = UncompressedPointRepresentation48<'a>;
    type SrcOwned = UncompressedPointRepresentation48OwnedInner;
    type DstOwned = UncompressedPointRepresentation48Owned;
}
pub struct UncompressedPointRepresentation48Owned {
    pub legacy_form: u8,
    pub x: Vec<u8>,
    pub y: Vec<u8>,
}
pub type UncompressedPointRepresentation48OwnedInner = (u8, (Vec<u8>, Vec<u8>));
impl View for UncompressedPointRepresentation48Owned {
    type V = SpecUncompressedPointRepresentation48;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation48 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl From<UncompressedPointRepresentation48Owned> for UncompressedPointRepresentation48OwnedInner {
    fn ex_from(m: UncompressedPointRepresentation48Owned) -> UncompressedPointRepresentation48OwnedInner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl From<UncompressedPointRepresentation48OwnedInner> for UncompressedPointRepresentation48Owned {
    fn ex_from(m: UncompressedPointRepresentation48OwnedInner) -> UncompressedPointRepresentation48Owned {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation48Owned {
            legacy_form,
            x,
            y,
        }
    }
}

pub struct SpecUncompressedPointRepresentation66 {
    pub legacy_form: u8,
    pub x: Seq<u8>,
    pub y: Seq<u8>,
}
pub type SpecUncompressedPointRepresentation66Inner = (u8, (Seq<u8>, Seq<u8>));
impl SpecFrom<SpecUncompressedPointRepresentation66> for SpecUncompressedPointRepresentation66Inner {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation66) -> SpecUncompressedPointRepresentation66Inner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl SpecFrom<SpecUncompressedPointRepresentation66Inner> for SpecUncompressedPointRepresentation66 {
    open spec fn spec_from(m: SpecUncompressedPointRepresentation66Inner) -> SpecUncompressedPointRepresentation66 {
        let (legacy_form, (x, y)) = m;
        SpecUncompressedPointRepresentation66 {
            legacy_form,
            x,
            y,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UncompressedPointRepresentation66<'a> {
    pub legacy_form: u8,
    pub x: &'a [u8],
    pub y: &'a [u8],
}
pub type UncompressedPointRepresentation66Inner<'a> = (u8, (&'a [u8], &'a [u8]));
impl View for UncompressedPointRepresentation66<'_> {
    type V = SpecUncompressedPointRepresentation66;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation66 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl<'a> From<UncompressedPointRepresentation66<'a>> for UncompressedPointRepresentation66Inner<'a> {
    fn ex_from(m: UncompressedPointRepresentation66<'a>) -> UncompressedPointRepresentation66Inner<'a> {
        (m.legacy_form, (m.x, m.y))
    }
}
impl<'a> From<UncompressedPointRepresentation66Inner<'a>> for UncompressedPointRepresentation66<'a> {
    fn ex_from(m: UncompressedPointRepresentation66Inner<'a>) -> UncompressedPointRepresentation66<'a> {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation66 {
            legacy_form,
            x,
            y,
        }
    }
}
pub struct UncompressedPointRepresentation66Mapper;
impl View for UncompressedPointRepresentation66Mapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for UncompressedPointRepresentation66Mapper {
    type Src = SpecUncompressedPointRepresentation66Inner;
    type Dst = SpecUncompressedPointRepresentation66;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for UncompressedPointRepresentation66Mapper {
    type Src<'a> = UncompressedPointRepresentation66Inner<'a>;
    type Dst<'a> = UncompressedPointRepresentation66<'a>;
    type SrcOwned = UncompressedPointRepresentation66OwnedInner;
    type DstOwned = UncompressedPointRepresentation66Owned;
}
pub struct UncompressedPointRepresentation66Owned {
    pub legacy_form: u8,
    pub x: Vec<u8>,
    pub y: Vec<u8>,
}
pub type UncompressedPointRepresentation66OwnedInner = (u8, (Vec<u8>, Vec<u8>));
impl View for UncompressedPointRepresentation66Owned {
    type V = SpecUncompressedPointRepresentation66;
    open spec fn view(&self) -> Self::V {
        SpecUncompressedPointRepresentation66 {
            legacy_form: self.legacy_form@,
            x: self.x@,
            y: self.y@,
        }
    }
}
impl From<UncompressedPointRepresentation66Owned> for UncompressedPointRepresentation66OwnedInner {
    fn ex_from(m: UncompressedPointRepresentation66Owned) -> UncompressedPointRepresentation66OwnedInner {
        (m.legacy_form, (m.x, m.y))
    }
}
impl From<UncompressedPointRepresentation66OwnedInner> for UncompressedPointRepresentation66Owned {
    fn ex_from(m: UncompressedPointRepresentation66OwnedInner) -> UncompressedPointRepresentation66Owned {
        let (legacy_form, (x, y)) = m;
        UncompressedPointRepresentation66Owned {
            legacy_form,
            x,
            y,
        }
    }
}

pub type SpecMontgomeryPoint32 = Seq<u8>;
pub type MontgomeryPoint32<'a> = &'a [u8];
pub type MontgomeryPoint32Owned = Vec<u8>;

pub type SpecMontgomeryForm56 = Seq<u8>;
pub type MontgomeryForm56<'a> = &'a [u8];
pub type MontgomeryForm56Owned = Vec<u8>;

pub struct SpecSeverDhParams {
    pub dh_p: SpecOpaque1Ffff,
    pub dh_g: SpecOpaque1Ffff,
    pub dh_ys: SpecOpaque1Ffff,
}
pub type SpecSeverDhParamsInner = (SpecOpaque1Ffff, (SpecOpaque1Ffff, SpecOpaque1Ffff));
impl SpecFrom<SpecSeverDhParams> for SpecSeverDhParamsInner {
    open spec fn spec_from(m: SpecSeverDhParams) -> SpecSeverDhParamsInner {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl SpecFrom<SpecSeverDhParamsInner> for SpecSeverDhParams {
    open spec fn spec_from(m: SpecSeverDhParamsInner) -> SpecSeverDhParams {
        let (dh_p, (dh_g, dh_ys)) = m;
        SpecSeverDhParams {
            dh_p,
            dh_g,
            dh_ys,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeverDhParams<'a> {
    pub dh_p: Opaque1Ffff<'a>,
    pub dh_g: Opaque1Ffff<'a>,
    pub dh_ys: Opaque1Ffff<'a>,
}
pub type SeverDhParamsInner<'a> = (Opaque1Ffff<'a>, (Opaque1Ffff<'a>, Opaque1Ffff<'a>));
impl View for SeverDhParams<'_> {
    type V = SpecSeverDhParams;
    open spec fn view(&self) -> Self::V {
        SpecSeverDhParams {
            dh_p: self.dh_p@,
            dh_g: self.dh_g@,
            dh_ys: self.dh_ys@,
        }
    }
}
impl<'a> From<SeverDhParams<'a>> for SeverDhParamsInner<'a> {
    fn ex_from(m: SeverDhParams<'a>) -> SeverDhParamsInner<'a> {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl<'a> From<SeverDhParamsInner<'a>> for SeverDhParams<'a> {
    fn ex_from(m: SeverDhParamsInner<'a>) -> SeverDhParams<'a> {
        let (dh_p, (dh_g, dh_ys)) = m;
        SeverDhParams {
            dh_p,
            dh_g,
            dh_ys,
        }
    }
}
pub struct SeverDhParamsMapper;
impl View for SeverDhParamsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverDhParamsMapper {
    type Src = SpecSeverDhParamsInner;
    type Dst = SpecSeverDhParams;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SeverDhParamsMapper {
    type Src<'a> = SeverDhParamsInner<'a>;
    type Dst<'a> = SeverDhParams<'a>;
    type SrcOwned = SeverDhParamsOwnedInner;
    type DstOwned = SeverDhParamsOwned;
}
pub struct SeverDhParamsOwned {
    pub dh_p: Opaque1FfffOwned,
    pub dh_g: Opaque1FfffOwned,
    pub dh_ys: Opaque1FfffOwned,
}
pub type SeverDhParamsOwnedInner = (Opaque1FfffOwned, (Opaque1FfffOwned, Opaque1FfffOwned));
impl View for SeverDhParamsOwned {
    type V = SpecSeverDhParams;
    open spec fn view(&self) -> Self::V {
        SpecSeverDhParams {
            dh_p: self.dh_p@,
            dh_g: self.dh_g@,
            dh_ys: self.dh_ys@,
        }
    }
}
impl From<SeverDhParamsOwned> for SeverDhParamsOwnedInner {
    fn ex_from(m: SeverDhParamsOwned) -> SeverDhParamsOwnedInner {
        (m.dh_p, (m.dh_g, m.dh_ys))
    }
}
impl From<SeverDhParamsOwnedInner> for SeverDhParamsOwned {
    fn ex_from(m: SeverDhParamsOwnedInner) -> SeverDhParamsOwned {
        let (dh_p, (dh_g, dh_ys)) = m;
        SeverDhParamsOwned {
            dh_p,
            dh_g,
            dh_ys,
        }
    }
}

pub type SpecKeyExchangeData = SpecOpaque1Ffff;
pub type KeyExchangeData<'a> = Opaque1Ffff<'a>;
pub type KeyExchangeDataOwned = Opaque1FfffOwned;

pub enum SpecKeyShareEntryKeyExchange {
    Secp256r1(SpecUncompressedPointRepresentation32),
    Secp384r1(SpecUncompressedPointRepresentation48),
    Secp521r1(SpecUncompressedPointRepresentation66),
    X25519(SpecMontgomeryPoint32),
    X448(SpecMontgomeryForm56),
    Ffdhe2048(SpecSeverDhParams),
    Ffdhe3072(SpecSeverDhParams),
    Ffdhe4096(SpecSeverDhParams),
    Ffdhe6144(SpecSeverDhParams),
    Ffdhe8192(SpecSeverDhParams),
    Unrecognized(SpecKeyExchangeData),
}
pub type SpecKeyShareEntryKeyExchangeInner = Either<SpecUncompressedPointRepresentation32, Either<SpecUncompressedPointRepresentation48, Either<SpecUncompressedPointRepresentation66, Either<SpecMontgomeryPoint32, Either<SpecMontgomeryForm56, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, Either<SpecSeverDhParams, SpecKeyExchangeData>>>>>>>>>>;
impl SpecFrom<SpecKeyShareEntryKeyExchange> for SpecKeyShareEntryKeyExchangeInner {
    open spec fn spec_from(m: SpecKeyShareEntryKeyExchange) -> SpecKeyShareEntryKeyExchangeInner {
        match m {
            SpecKeyShareEntryKeyExchange::Secp256r1(m) => Either::Left(m),
            SpecKeyShareEntryKeyExchange::Secp384r1(m) => Either::Right(Either::Left(m)),
            SpecKeyShareEntryKeyExchange::Secp521r1(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecKeyShareEntryKeyExchange::X25519(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecKeyShareEntryKeyExchange::X448(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecKeyShareEntryKeyExchange::Ffdhe2048(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecKeyShareEntryKeyExchange::Ffdhe3072(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe4096(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe6144(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecKeyShareEntryKeyExchange::Ffdhe8192(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecKeyShareEntryKeyExchange::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }
}
impl SpecFrom<SpecKeyShareEntryKeyExchangeInner> for SpecKeyShareEntryKeyExchange {
    open spec fn spec_from(m: SpecKeyShareEntryKeyExchangeInner) -> SpecKeyShareEntryKeyExchange {
        match m {
            Either::Left(m) => SpecKeyShareEntryKeyExchange::Secp256r1(m),
            Either::Right(Either::Left(m)) => SpecKeyShareEntryKeyExchange::Secp384r1(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecKeyShareEntryKeyExchange::Secp521r1(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecKeyShareEntryKeyExchange::X25519(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecKeyShareEntryKeyExchange::X448(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecKeyShareEntryKeyExchange::Ffdhe2048(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecKeyShareEntryKeyExchange::Ffdhe3072(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecKeyShareEntryKeyExchange::Ffdhe4096(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecKeyShareEntryKeyExchange::Ffdhe6144(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecKeyShareEntryKeyExchange::Ffdhe8192(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => SpecKeyShareEntryKeyExchange::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KeyShareEntryKeyExchange<'a> {
    Secp256r1(UncompressedPointRepresentation32<'a>),
    Secp384r1(UncompressedPointRepresentation48<'a>),
    Secp521r1(UncompressedPointRepresentation66<'a>),
    X25519(MontgomeryPoint32<'a>),
    X448(MontgomeryForm56<'a>),
    Ffdhe2048(SeverDhParams<'a>),
    Ffdhe3072(SeverDhParams<'a>),
    Ffdhe4096(SeverDhParams<'a>),
    Ffdhe6144(SeverDhParams<'a>),
    Ffdhe8192(SeverDhParams<'a>),
    Unrecognized(KeyExchangeData<'a>),
}
pub type KeyShareEntryKeyExchangeInner<'a> = Either<UncompressedPointRepresentation32<'a>, Either<UncompressedPointRepresentation48<'a>, Either<UncompressedPointRepresentation66<'a>, Either<MontgomeryPoint32<'a>, Either<MontgomeryForm56<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, Either<SeverDhParams<'a>, KeyExchangeData<'a>>>>>>>>>>>;
impl View for KeyShareEntryKeyExchange<'_> {
    type V = SpecKeyShareEntryKeyExchange;
    open spec fn view(&self) -> Self::V {
        match self {
            KeyShareEntryKeyExchange::Secp256r1(m) => SpecKeyShareEntryKeyExchange::Secp256r1(m@),
            KeyShareEntryKeyExchange::Secp384r1(m) => SpecKeyShareEntryKeyExchange::Secp384r1(m@),
            KeyShareEntryKeyExchange::Secp521r1(m) => SpecKeyShareEntryKeyExchange::Secp521r1(m@),
            KeyShareEntryKeyExchange::X25519(m) => SpecKeyShareEntryKeyExchange::X25519(m@),
            KeyShareEntryKeyExchange::X448(m) => SpecKeyShareEntryKeyExchange::X448(m@),
            KeyShareEntryKeyExchange::Ffdhe2048(m) => SpecKeyShareEntryKeyExchange::Ffdhe2048(m@),
            KeyShareEntryKeyExchange::Ffdhe3072(m) => SpecKeyShareEntryKeyExchange::Ffdhe3072(m@),
            KeyShareEntryKeyExchange::Ffdhe4096(m) => SpecKeyShareEntryKeyExchange::Ffdhe4096(m@),
            KeyShareEntryKeyExchange::Ffdhe6144(m) => SpecKeyShareEntryKeyExchange::Ffdhe6144(m@),
            KeyShareEntryKeyExchange::Ffdhe8192(m) => SpecKeyShareEntryKeyExchange::Ffdhe8192(m@),
            KeyShareEntryKeyExchange::Unrecognized(m) => SpecKeyShareEntryKeyExchange::Unrecognized(m@),
        }
    }
}
impl<'a> From<KeyShareEntryKeyExchange<'a>> for KeyShareEntryKeyExchangeInner<'a> {
    fn ex_from(m: KeyShareEntryKeyExchange<'a>) -> KeyShareEntryKeyExchangeInner<'a> {
        match m {
            KeyShareEntryKeyExchange::Secp256r1(m) => Either::Left(m),
            KeyShareEntryKeyExchange::Secp384r1(m) => Either::Right(Either::Left(m)),
            KeyShareEntryKeyExchange::Secp521r1(m) => Either::Right(Either::Right(Either::Left(m))),
            KeyShareEntryKeyExchange::X25519(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            KeyShareEntryKeyExchange::X448(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            KeyShareEntryKeyExchange::Ffdhe2048(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            KeyShareEntryKeyExchange::Ffdhe3072(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            KeyShareEntryKeyExchange::Ffdhe4096(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            KeyShareEntryKeyExchange::Ffdhe6144(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            KeyShareEntryKeyExchange::Ffdhe8192(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            KeyShareEntryKeyExchange::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }
}
impl<'a> From<KeyShareEntryKeyExchangeInner<'a>> for KeyShareEntryKeyExchange<'a> {
    fn ex_from(m: KeyShareEntryKeyExchangeInner<'a>) -> KeyShareEntryKeyExchange<'a> {
        match m {
            Either::Left(m) => KeyShareEntryKeyExchange::Secp256r1(m),
            Either::Right(Either::Left(m)) => KeyShareEntryKeyExchange::Secp384r1(m),
            Either::Right(Either::Right(Either::Left(m))) => KeyShareEntryKeyExchange::Secp521r1(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => KeyShareEntryKeyExchange::X25519(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => KeyShareEntryKeyExchange::X448(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => KeyShareEntryKeyExchange::Ffdhe2048(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => KeyShareEntryKeyExchange::Ffdhe3072(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => KeyShareEntryKeyExchange::Ffdhe4096(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => KeyShareEntryKeyExchange::Ffdhe6144(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => KeyShareEntryKeyExchange::Ffdhe8192(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => KeyShareEntryKeyExchange::Unrecognized(m),
        }
    }
}
pub struct KeyShareEntryKeyExchangeMapper;
impl View for KeyShareEntryKeyExchangeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareEntryKeyExchangeMapper {
    type Src = SpecKeyShareEntryKeyExchangeInner;
    type Dst = SpecKeyShareEntryKeyExchange;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for KeyShareEntryKeyExchangeMapper {
    type Src<'a> = KeyShareEntryKeyExchangeInner<'a>;
    type Dst<'a> = KeyShareEntryKeyExchange<'a>;
    type SrcOwned = KeyShareEntryKeyExchangeOwnedInner;
    type DstOwned = KeyShareEntryKeyExchangeOwned;
}
pub enum KeyShareEntryKeyExchangeOwned {
    Secp256r1(UncompressedPointRepresentation32Owned),
    Secp384r1(UncompressedPointRepresentation48Owned),
    Secp521r1(UncompressedPointRepresentation66Owned),
    X25519(MontgomeryPoint32Owned),
    X448(MontgomeryForm56Owned),
    Ffdhe2048(SeverDhParamsOwned),
    Ffdhe3072(SeverDhParamsOwned),
    Ffdhe4096(SeverDhParamsOwned),
    Ffdhe6144(SeverDhParamsOwned),
    Ffdhe8192(SeverDhParamsOwned),
    Unrecognized(KeyExchangeDataOwned),
}
pub type KeyShareEntryKeyExchangeOwnedInner = Either<UncompressedPointRepresentation32Owned, Either<UncompressedPointRepresentation48Owned, Either<UncompressedPointRepresentation66Owned, Either<MontgomeryPoint32Owned, Either<MontgomeryForm56Owned, Either<SeverDhParamsOwned, Either<SeverDhParamsOwned, Either<SeverDhParamsOwned, Either<SeverDhParamsOwned, Either<SeverDhParamsOwned, KeyExchangeDataOwned>>>>>>>>>>;
impl View for KeyShareEntryKeyExchangeOwned {
    type V = SpecKeyShareEntryKeyExchange;
    open spec fn view(&self) -> Self::V {
        match self {
            KeyShareEntryKeyExchangeOwned::Secp256r1(m) => SpecKeyShareEntryKeyExchange::Secp256r1(m@),
            KeyShareEntryKeyExchangeOwned::Secp384r1(m) => SpecKeyShareEntryKeyExchange::Secp384r1(m@),
            KeyShareEntryKeyExchangeOwned::Secp521r1(m) => SpecKeyShareEntryKeyExchange::Secp521r1(m@),
            KeyShareEntryKeyExchangeOwned::X25519(m) => SpecKeyShareEntryKeyExchange::X25519(m@),
            KeyShareEntryKeyExchangeOwned::X448(m) => SpecKeyShareEntryKeyExchange::X448(m@),
            KeyShareEntryKeyExchangeOwned::Ffdhe2048(m) => SpecKeyShareEntryKeyExchange::Ffdhe2048(m@),
            KeyShareEntryKeyExchangeOwned::Ffdhe3072(m) => SpecKeyShareEntryKeyExchange::Ffdhe3072(m@),
            KeyShareEntryKeyExchangeOwned::Ffdhe4096(m) => SpecKeyShareEntryKeyExchange::Ffdhe4096(m@),
            KeyShareEntryKeyExchangeOwned::Ffdhe6144(m) => SpecKeyShareEntryKeyExchange::Ffdhe6144(m@),
            KeyShareEntryKeyExchangeOwned::Ffdhe8192(m) => SpecKeyShareEntryKeyExchange::Ffdhe8192(m@),
            KeyShareEntryKeyExchangeOwned::Unrecognized(m) => SpecKeyShareEntryKeyExchange::Unrecognized(m@),
        }
    }
}
impl From<KeyShareEntryKeyExchangeOwned> for KeyShareEntryKeyExchangeOwnedInner {
    fn ex_from(m: KeyShareEntryKeyExchangeOwned) -> KeyShareEntryKeyExchangeOwnedInner {
        match m {
            KeyShareEntryKeyExchangeOwned::Secp256r1(m) => Either::Left(m),
            KeyShareEntryKeyExchangeOwned::Secp384r1(m) => Either::Right(Either::Left(m)),
            KeyShareEntryKeyExchangeOwned::Secp521r1(m) => Either::Right(Either::Right(Either::Left(m))),
            KeyShareEntryKeyExchangeOwned::X25519(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            KeyShareEntryKeyExchangeOwned::X448(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            KeyShareEntryKeyExchangeOwned::Ffdhe2048(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            KeyShareEntryKeyExchangeOwned::Ffdhe3072(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            KeyShareEntryKeyExchangeOwned::Ffdhe4096(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            KeyShareEntryKeyExchangeOwned::Ffdhe6144(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            KeyShareEntryKeyExchangeOwned::Ffdhe8192(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            KeyShareEntryKeyExchangeOwned::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))),
        }
    }
}
impl From<KeyShareEntryKeyExchangeOwnedInner> for KeyShareEntryKeyExchangeOwned {
    fn ex_from(m: KeyShareEntryKeyExchangeOwnedInner) -> KeyShareEntryKeyExchangeOwned {
        match m {
            Either::Left(m) => KeyShareEntryKeyExchangeOwned::Secp256r1(m),
            Either::Right(Either::Left(m)) => KeyShareEntryKeyExchangeOwned::Secp384r1(m),
            Either::Right(Either::Right(Either::Left(m))) => KeyShareEntryKeyExchangeOwned::Secp521r1(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => KeyShareEntryKeyExchangeOwned::X25519(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => KeyShareEntryKeyExchangeOwned::X448(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => KeyShareEntryKeyExchangeOwned::Ffdhe2048(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => KeyShareEntryKeyExchangeOwned::Ffdhe3072(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => KeyShareEntryKeyExchangeOwned::Ffdhe4096(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => KeyShareEntryKeyExchangeOwned::Ffdhe6144(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => KeyShareEntryKeyExchangeOwned::Ffdhe8192(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))) => KeyShareEntryKeyExchangeOwned::Unrecognized(m),
        }
    }
}

pub struct SpecKeyShareEntry {
    pub group: SpecNamedGroup,
    pub l: SpecUint1Ffff,
    pub key_exchange: SpecKeyShareEntryKeyExchange,
}
pub type SpecKeyShareEntryInner = ((SpecNamedGroup, SpecUint1Ffff), SpecKeyShareEntryKeyExchange);
impl SpecFrom<SpecKeyShareEntry> for SpecKeyShareEntryInner {
    open spec fn spec_from(m: SpecKeyShareEntry) -> SpecKeyShareEntryInner {
        ((m.group, m.l), m.key_exchange)
    }
}
impl SpecFrom<SpecKeyShareEntryInner> for SpecKeyShareEntry {
    open spec fn spec_from(m: SpecKeyShareEntryInner) -> SpecKeyShareEntry {
        let ((group, l), key_exchange) = m;
        SpecKeyShareEntry {
            group,
            l,
            key_exchange,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyShareEntry<'a> {
    pub group: NamedGroup,
    pub l: Uint1Ffff,
    pub key_exchange: KeyShareEntryKeyExchange<'a>,
}
pub type KeyShareEntryInner<'a> = ((NamedGroup, Uint1Ffff), KeyShareEntryKeyExchange<'a>);
impl View for KeyShareEntry<'_> {
    type V = SpecKeyShareEntry;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareEntry {
            group: self.group@,
            l: self.l@,
            key_exchange: self.key_exchange@,
        }
    }
}
impl<'a> From<KeyShareEntry<'a>> for KeyShareEntryInner<'a> {
    fn ex_from(m: KeyShareEntry<'a>) -> KeyShareEntryInner<'a> {
        ((m.group, m.l), m.key_exchange)
    }
}
impl<'a> From<KeyShareEntryInner<'a>> for KeyShareEntry<'a> {
    fn ex_from(m: KeyShareEntryInner<'a>) -> KeyShareEntry<'a> {
        let ((group, l), key_exchange) = m;
        KeyShareEntry {
            group,
            l,
            key_exchange,
        }
    }
}
pub struct KeyShareEntryMapper;
impl View for KeyShareEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareEntryMapper {
    type Src = SpecKeyShareEntryInner;
    type Dst = SpecKeyShareEntry;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for KeyShareEntryMapper {
    type Src<'a> = KeyShareEntryInner<'a>;
    type Dst<'a> = KeyShareEntry<'a>;
    type SrcOwned = KeyShareEntryOwnedInner;
    type DstOwned = KeyShareEntryOwned;
}
pub struct KeyShareEntryOwned {
    pub group: NamedGroupOwned,
    pub l: Uint1FfffOwned,
    pub key_exchange: KeyShareEntryKeyExchangeOwned,
}
pub type KeyShareEntryOwnedInner = ((NamedGroupOwned, Uint1FfffOwned), KeyShareEntryKeyExchangeOwned);
impl View for KeyShareEntryOwned {
    type V = SpecKeyShareEntry;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareEntry {
            group: self.group@,
            l: self.l@,
            key_exchange: self.key_exchange@,
        }
    }
}
impl From<KeyShareEntryOwned> for KeyShareEntryOwnedInner {
    fn ex_from(m: KeyShareEntryOwned) -> KeyShareEntryOwnedInner {
        ((m.group, m.l), m.key_exchange)
    }
}
impl From<KeyShareEntryOwnedInner> for KeyShareEntryOwned {
    fn ex_from(m: KeyShareEntryOwnedInner) -> KeyShareEntryOwned {
        let ((group, l), key_exchange) = m;
        KeyShareEntryOwned {
            group,
            l,
            key_exchange,
        }
    }
}

pub type SpecKeyShareClientHelloClientShares = Seq<SpecKeyShareEntry>;
pub type KeyShareClientHelloClientShares<'a> = RepeatResult<KeyShareEntry<'a>>;
pub type KeyShareClientHelloClientSharesOwned = RepeatResult<KeyShareEntryOwned>;

pub struct SpecKeyShareClientHello {
    pub l: SpecUint0Ffff,
    pub client_shares: SpecKeyShareClientHelloClientShares,
}
pub type SpecKeyShareClientHelloInner = (SpecUint0Ffff, SpecKeyShareClientHelloClientShares);
impl SpecFrom<SpecKeyShareClientHello> for SpecKeyShareClientHelloInner {
    open spec fn spec_from(m: SpecKeyShareClientHello) -> SpecKeyShareClientHelloInner {
        (m.l, m.client_shares)
    }
}
impl SpecFrom<SpecKeyShareClientHelloInner> for SpecKeyShareClientHello {
    open spec fn spec_from(m: SpecKeyShareClientHelloInner) -> SpecKeyShareClientHello {
        let (l, client_shares) = m;
        SpecKeyShareClientHello {
            l,
            client_shares,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyShareClientHello<'a> {
    pub l: Uint0Ffff,
    pub client_shares: KeyShareClientHelloClientShares<'a>,
}
pub type KeyShareClientHelloInner<'a> = (Uint0Ffff, KeyShareClientHelloClientShares<'a>);
impl View for KeyShareClientHello<'_> {
    type V = SpecKeyShareClientHello;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareClientHello {
            l: self.l@,
            client_shares: self.client_shares@,
        }
    }
}
impl<'a> From<KeyShareClientHello<'a>> for KeyShareClientHelloInner<'a> {
    fn ex_from(m: KeyShareClientHello<'a>) -> KeyShareClientHelloInner<'a> {
        (m.l, m.client_shares)
    }
}
impl<'a> From<KeyShareClientHelloInner<'a>> for KeyShareClientHello<'a> {
    fn ex_from(m: KeyShareClientHelloInner<'a>) -> KeyShareClientHello<'a> {
        let (l, client_shares) = m;
        KeyShareClientHello {
            l,
            client_shares,
        }
    }
}
pub struct KeyShareClientHelloMapper;
impl View for KeyShareClientHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyShareClientHelloMapper {
    type Src = SpecKeyShareClientHelloInner;
    type Dst = SpecKeyShareClientHello;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for KeyShareClientHelloMapper {
    type Src<'a> = KeyShareClientHelloInner<'a>;
    type Dst<'a> = KeyShareClientHello<'a>;
    type SrcOwned = KeyShareClientHelloOwnedInner;
    type DstOwned = KeyShareClientHelloOwned;
}
pub struct KeyShareClientHelloOwned {
    pub l: Uint0FfffOwned,
    pub client_shares: KeyShareClientHelloClientSharesOwned,
}
pub type KeyShareClientHelloOwnedInner = (Uint0FfffOwned, KeyShareClientHelloClientSharesOwned);
impl View for KeyShareClientHelloOwned {
    type V = SpecKeyShareClientHello;
    open spec fn view(&self) -> Self::V {
        SpecKeyShareClientHello {
            l: self.l@,
            client_shares: self.client_shares@,
        }
    }
}
impl From<KeyShareClientHelloOwned> for KeyShareClientHelloOwnedInner {
    fn ex_from(m: KeyShareClientHelloOwned) -> KeyShareClientHelloOwnedInner {
        (m.l, m.client_shares)
    }
}
impl From<KeyShareClientHelloOwnedInner> for KeyShareClientHelloOwned {
    fn ex_from(m: KeyShareClientHelloOwnedInner) -> KeyShareClientHelloOwned {
        let (l, client_shares) = m;
        KeyShareClientHelloOwned {
            l,
            client_shares,
        }
    }
}

pub enum SpecClientHelloExtensionExtensionData {
    ServerName(SpecServerNameList),
    MaxFragmentLength(SpecMaxFragmentLength),
    StatusRequest(SpecCertificateStatusRequest),
    SupportedGroups(SpecNamedGroupList),
    ECPointFormats(SpecEcPointFormatList),
    SignatureAlgorithms(SpecSignatureSchemeList),
    UseSRTP(SpecUseSrtpData),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SigedCertificateTimestamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(SpecPaddingExtension),
    EncryptThenMac(SpecEmpty),
    ExtendedMasterSecret(SpecEmpty),
    SessionTicket(Seq<u8>),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    EarlyData(SpecEmpty),
    SupportedVersions(SpecSupportedVersionsClient),
    Cookie(SpecCookie),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    PostHandshakeAuth(SpecEmpty),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    KeyShare(SpecKeyShareClientHello),
    Unrecognized(Seq<u8>),
}
pub type SpecClientHelloExtensionExtensionDataInner = Either<SpecServerNameList, Either<SpecMaxFragmentLength, Either<SpecCertificateStatusRequest, Either<SpecNamedGroupList, Either<SpecEcPointFormatList, Either<SpecSignatureSchemeList, Either<SpecUseSrtpData, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecPaddingExtension, Either<SpecEmpty, Either<SpecEmpty, Either<Seq<u8>, Either<SpecPreSharedKeyClientExtension, Either<SpecEmpty, Either<SpecSupportedVersionsClient, Either<SpecCookie, Either<SpecPskKeyExchangeModes, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecEmpty, Either<SpecSignatureSchemeList, Either<SpecKeyShareClientHello, Seq<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl SpecFrom<SpecClientHelloExtensionExtensionData> for SpecClientHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionData) -> SpecClientHelloExtensionExtensionDataInner {
        match m {
            SpecClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecClientHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecClientHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl SpecFrom<SpecClientHelloExtensionExtensionDataInner> for SpecClientHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecClientHelloExtensionExtensionDataInner) -> SpecClientHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecClientHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SpecClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClientHelloExtensionExtensionData<'a> {
    ServerName(ServerNameList<'a>),
    MaxFragmentLength(MaxFragmentLength),
    StatusRequest(CertificateStatusRequest<'a>),
    SupportedGroups(NamedGroupList),
    ECPointFormats(EcPointFormatList),
    SignatureAlgorithms(SignatureSchemeList),
    UseSRTP(UseSrtpData<'a>),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SigedCertificateTimestamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(PaddingExtension),
    EncryptThenMac(Empty<'a>),
    ExtendedMasterSecret(Empty<'a>),
    SessionTicket(&'a [u8]),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    EarlyData(Empty<'a>),
    SupportedVersions(SupportedVersionsClient),
    Cookie(Cookie<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    PostHandshakeAuth(Empty<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    KeyShare(KeyShareClientHello<'a>),
    Unrecognized(&'a [u8]),
}
pub type ClientHelloExtensionExtensionDataInner<'a> = Either<ServerNameList<'a>, Either<MaxFragmentLength, Either<CertificateStatusRequest<'a>, Either<NamedGroupList, Either<EcPointFormatList, Either<SignatureSchemeList, Either<UseSrtpData<'a>, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<PaddingExtension, Either<Empty<'a>, Either<Empty<'a>, Either<&'a [u8], Either<PreSharedKeyClientExtension<'a>, Either<Empty<'a>, Either<SupportedVersionsClient, Either<Cookie<'a>, Either<PskKeyExchangeModes, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<Empty<'a>, Either<SignatureSchemeList, Either<KeyShareClientHello<'a>, &'a [u8]>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for ClientHelloExtensionExtensionData<'_> {
    type V = SpecClientHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionExtensionData::ServerName(m) => SpecClientHelloExtensionExtensionData::ServerName(m@),
            ClientHelloExtensionExtensionData::MaxFragmentLength(m) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m@),
            ClientHelloExtensionExtensionData::StatusRequest(m) => SpecClientHelloExtensionExtensionData::StatusRequest(m@),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => SpecClientHelloExtensionExtensionData::SupportedGroups(m@),
            ClientHelloExtensionExtensionData::ECPointFormats(m) => SpecClientHelloExtensionExtensionData::ECPointFormats(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m@),
            ClientHelloExtensionExtensionData::UseSRTP(m) => SpecClientHelloExtensionExtensionData::UseSRTP(m@),
            ClientHelloExtensionExtensionData::Heartbeat(m) => SpecClientHelloExtensionExtensionData::Heartbeat(m@),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m@),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m@),
            ClientHelloExtensionExtensionData::Padding(m) => SpecClientHelloExtensionExtensionData::Padding(m@),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m@),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            ClientHelloExtensionExtensionData::SessionTicket(m) => SpecClientHelloExtensionExtensionData::SessionTicket(m@),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => SpecClientHelloExtensionExtensionData::PreSharedKey(m@),
            ClientHelloExtensionExtensionData::EarlyData(m) => SpecClientHelloExtensionExtensionData::EarlyData(m@),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => SpecClientHelloExtensionExtensionData::SupportedVersions(m@),
            ClientHelloExtensionExtensionData::Cookie(m) => SpecClientHelloExtensionExtensionData::Cookie(m@),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m@),
            ClientHelloExtensionExtensionData::OidFilters(m) => SpecClientHelloExtensionExtensionData::OidFilters(m@),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m@),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            ClientHelloExtensionExtensionData::KeyShare(m) => SpecClientHelloExtensionExtensionData::KeyShare(m@),
            ClientHelloExtensionExtensionData::Unrecognized(m) => SpecClientHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}
impl<'a> From<ClientHelloExtensionExtensionData<'a>> for ClientHelloExtensionExtensionDataInner<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionData<'a>) -> ClientHelloExtensionExtensionDataInner<'a> {
        match m {
            ClientHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            ClientHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            ClientHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            ClientHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ClientHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ClientHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ClientHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ClientHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ClientHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ClientHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ClientHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ClientHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ClientHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ClientHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ClientHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ClientHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ClientHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            ClientHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl<'a> From<ClientHelloExtensionExtensionDataInner<'a>> for ClientHelloExtensionExtensionData<'a> {
    fn ex_from(m: ClientHelloExtensionExtensionDataInner<'a>) -> ClientHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => ClientHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ClientHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ClientHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ClientHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ClientHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ClientHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ClientHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ClientHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ClientHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ClientHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ClientHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ClientHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ClientHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ClientHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ClientHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ClientHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => ClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => ClientHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => ClientHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
pub struct ClientHelloExtensionExtensionDataMapper;
impl View for ClientHelloExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionExtensionDataMapper {
    type Src = SpecClientHelloExtensionExtensionDataInner;
    type Dst = SpecClientHelloExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientHelloExtensionExtensionDataMapper {
    type Src<'a> = ClientHelloExtensionExtensionDataInner<'a>;
    type Dst<'a> = ClientHelloExtensionExtensionData<'a>;
    type SrcOwned = ClientHelloExtensionExtensionDataOwnedInner;
    type DstOwned = ClientHelloExtensionExtensionDataOwned;
}
pub enum ClientHelloExtensionExtensionDataOwned {
    ServerName(ServerNameListOwned),
    MaxFragmentLength(MaxFragmentLengthOwned),
    StatusRequest(CertificateStatusRequestOwned),
    SupportedGroups(NamedGroupListOwned),
    ECPointFormats(EcPointFormatListOwned),
    SignatureAlgorithms(SignatureSchemeListOwned),
    UseSRTP(UseSrtpDataOwned),
    Heartbeat(HeartbeatModeOwned),
    ApplicationLayerProtocolNegotiation(ProtocolNameListOwned),
    SigedCertificateTimestamp(SignedCertificateTimestampListOwned),
    ClientCertificateType(ClientCertTypeClientExtensionOwned),
    ServerCertificateType(ServerCertTypeClientExtensionOwned),
    Padding(PaddingExtensionOwned),
    EncryptThenMac(EmptyOwned),
    ExtendedMasterSecret(EmptyOwned),
    SessionTicket(Vec<u8>),
    PreSharedKey(PreSharedKeyClientExtensionOwned),
    EarlyData(EmptyOwned),
    SupportedVersions(SupportedVersionsClientOwned),
    Cookie(CookieOwned),
    PskKeyExchangeModes(PskKeyExchangeModesOwned),
    CertificateAuthorities(CertificateAuthoritiesExtensionOwned),
    OidFilters(OidFilterExtensionOwned),
    PostHandshakeAuth(EmptyOwned),
    SignatureAlgorithmsCert(SignatureSchemeListOwned),
    KeyShare(KeyShareClientHelloOwned),
    Unrecognized(Vec<u8>),
}
pub type ClientHelloExtensionExtensionDataOwnedInner = Either<ServerNameListOwned, Either<MaxFragmentLengthOwned, Either<CertificateStatusRequestOwned, Either<NamedGroupListOwned, Either<EcPointFormatListOwned, Either<SignatureSchemeListOwned, Either<UseSrtpDataOwned, Either<HeartbeatModeOwned, Either<ProtocolNameListOwned, Either<SignedCertificateTimestampListOwned, Either<ClientCertTypeClientExtensionOwned, Either<ServerCertTypeClientExtensionOwned, Either<PaddingExtensionOwned, Either<EmptyOwned, Either<EmptyOwned, Either<Vec<u8>, Either<PreSharedKeyClientExtensionOwned, Either<EmptyOwned, Either<SupportedVersionsClientOwned, Either<CookieOwned, Either<PskKeyExchangeModesOwned, Either<CertificateAuthoritiesExtensionOwned, Either<OidFilterExtensionOwned, Either<EmptyOwned, Either<SignatureSchemeListOwned, Either<KeyShareClientHelloOwned, Vec<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for ClientHelloExtensionExtensionDataOwned {
    type V = SpecClientHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            ClientHelloExtensionExtensionDataOwned::ServerName(m) => SpecClientHelloExtensionExtensionData::ServerName(m@),
            ClientHelloExtensionExtensionDataOwned::MaxFragmentLength(m) => SpecClientHelloExtensionExtensionData::MaxFragmentLength(m@),
            ClientHelloExtensionExtensionDataOwned::StatusRequest(m) => SpecClientHelloExtensionExtensionData::StatusRequest(m@),
            ClientHelloExtensionExtensionDataOwned::SupportedGroups(m) => SpecClientHelloExtensionExtensionData::SupportedGroups(m@),
            ClientHelloExtensionExtensionDataOwned::ECPointFormats(m) => SpecClientHelloExtensionExtensionData::ECPointFormats(m@),
            ClientHelloExtensionExtensionDataOwned::SignatureAlgorithms(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithms(m@),
            ClientHelloExtensionExtensionDataOwned::UseSRTP(m) => SpecClientHelloExtensionExtensionData::UseSRTP(m@),
            ClientHelloExtensionExtensionDataOwned::Heartbeat(m) => SpecClientHelloExtensionExtensionData::Heartbeat(m@),
            ClientHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m) => SpecClientHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            ClientHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m) => SpecClientHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            ClientHelloExtensionExtensionDataOwned::ClientCertificateType(m) => SpecClientHelloExtensionExtensionData::ClientCertificateType(m@),
            ClientHelloExtensionExtensionDataOwned::ServerCertificateType(m) => SpecClientHelloExtensionExtensionData::ServerCertificateType(m@),
            ClientHelloExtensionExtensionDataOwned::Padding(m) => SpecClientHelloExtensionExtensionData::Padding(m@),
            ClientHelloExtensionExtensionDataOwned::EncryptThenMac(m) => SpecClientHelloExtensionExtensionData::EncryptThenMac(m@),
            ClientHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m) => SpecClientHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            ClientHelloExtensionExtensionDataOwned::SessionTicket(m) => SpecClientHelloExtensionExtensionData::SessionTicket(m@),
            ClientHelloExtensionExtensionDataOwned::PreSharedKey(m) => SpecClientHelloExtensionExtensionData::PreSharedKey(m@),
            ClientHelloExtensionExtensionDataOwned::EarlyData(m) => SpecClientHelloExtensionExtensionData::EarlyData(m@),
            ClientHelloExtensionExtensionDataOwned::SupportedVersions(m) => SpecClientHelloExtensionExtensionData::SupportedVersions(m@),
            ClientHelloExtensionExtensionDataOwned::Cookie(m) => SpecClientHelloExtensionExtensionData::Cookie(m@),
            ClientHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m) => SpecClientHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            ClientHelloExtensionExtensionDataOwned::CertificateAuthorities(m) => SpecClientHelloExtensionExtensionData::CertificateAuthorities(m@),
            ClientHelloExtensionExtensionDataOwned::OidFilters(m) => SpecClientHelloExtensionExtensionData::OidFilters(m@),
            ClientHelloExtensionExtensionDataOwned::PostHandshakeAuth(m) => SpecClientHelloExtensionExtensionData::PostHandshakeAuth(m@),
            ClientHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m) => SpecClientHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            ClientHelloExtensionExtensionDataOwned::KeyShare(m) => SpecClientHelloExtensionExtensionData::KeyShare(m@),
            ClientHelloExtensionExtensionDataOwned::Unrecognized(m) => SpecClientHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}
impl From<ClientHelloExtensionExtensionDataOwned> for ClientHelloExtensionExtensionDataOwnedInner {
    fn ex_from(m: ClientHelloExtensionExtensionDataOwned) -> ClientHelloExtensionExtensionDataOwnedInner {
        match m {
            ClientHelloExtensionExtensionDataOwned::ServerName(m) => Either::Left(m),
            ClientHelloExtensionExtensionDataOwned::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            ClientHelloExtensionExtensionDataOwned::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            ClientHelloExtensionExtensionDataOwned::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            ClientHelloExtensionExtensionDataOwned::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            ClientHelloExtensionExtensionDataOwned::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            ClientHelloExtensionExtensionDataOwned::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            ClientHelloExtensionExtensionDataOwned::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            ClientHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            ClientHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            ClientHelloExtensionExtensionDataOwned::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            ClientHelloExtensionExtensionDataOwned::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            ClientHelloExtensionExtensionDataOwned::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            ClientHelloExtensionExtensionDataOwned::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            ClientHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            ClientHelloExtensionExtensionDataOwned::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl From<ClientHelloExtensionExtensionDataOwnedInner> for ClientHelloExtensionExtensionDataOwned {
    fn ex_from(m: ClientHelloExtensionExtensionDataOwnedInner) -> ClientHelloExtensionExtensionDataOwned {
        match m {
            Either::Left(m) => ClientHelloExtensionExtensionDataOwned::ServerName(m),
            Either::Right(Either::Left(m)) => ClientHelloExtensionExtensionDataOwned::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => ClientHelloExtensionExtensionDataOwned::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => ClientHelloExtensionExtensionDataOwned::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => ClientHelloExtensionExtensionDataOwned::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => ClientHelloExtensionExtensionDataOwned::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => ClientHelloExtensionExtensionDataOwned::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => ClientHelloExtensionExtensionDataOwned::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => ClientHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => ClientHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => ClientHelloExtensionExtensionDataOwned::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => ClientHelloExtensionExtensionDataOwned::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => ClientHelloExtensionExtensionDataOwned::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => ClientHelloExtensionExtensionDataOwned::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => ClientHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => ClientHelloExtensionExtensionDataOwned::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => ClientHelloExtensionExtensionDataOwned::Unrecognized(m),
        }
    }
}

pub type SpecUint0Fffe = u16;
pub type Uint0Fffe = u16;
pub type Uint0FffeOwned = u16;


#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum KeyUpdateRequest {
    UpdateNotRequested = 0,
UpdateRequested = 1
}
pub type SpecKeyUpdateRequest = KeyUpdateRequest;
pub type KeyUpdateRequestOwned = KeyUpdateRequest;

pub type KeyUpdateRequestInner = u8;

impl View for KeyUpdateRequest {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<KeyUpdateRequestInner> for KeyUpdateRequest {
    type Error = ();

    open spec fn spec_try_from(v: KeyUpdateRequestInner) -> Result<KeyUpdateRequest, ()> {
        match v {
            0u8 => Ok(KeyUpdateRequest::UpdateNotRequested),
            1u8 => Ok(KeyUpdateRequest::UpdateRequested),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<KeyUpdateRequest> for KeyUpdateRequestInner {
    type Error = ();

    open spec fn spec_try_from(v: KeyUpdateRequest) -> Result<KeyUpdateRequestInner, ()> {
        match v {
            KeyUpdateRequest::UpdateNotRequested => Ok(0u8),
            KeyUpdateRequest::UpdateRequested => Ok(1u8),
        }
    }
}

impl TryFrom<KeyUpdateRequestInner> for KeyUpdateRequest {
    type Error = ();

    fn ex_try_from(v: KeyUpdateRequestInner) -> Result<KeyUpdateRequest, ()> {
        match v {
            0u8 => Ok(KeyUpdateRequest::UpdateNotRequested),
            1u8 => Ok(KeyUpdateRequest::UpdateRequested),
            _ => Err(()),
        }
    }
}

impl TryFrom<KeyUpdateRequest> for KeyUpdateRequestInner {
    type Error = ();

    fn ex_try_from(v: KeyUpdateRequest) -> Result<KeyUpdateRequestInner, ()> {
        match v {
            KeyUpdateRequest::UpdateNotRequested => Ok(0u8),
            KeyUpdateRequest::UpdateRequested => Ok(1u8),
        }
    }
}

pub struct KeyUpdateRequestMapper;

impl View for KeyUpdateRequestMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for KeyUpdateRequestMapper {
    type Src = KeyUpdateRequestInner;
    type Dst = KeyUpdateRequest;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for KeyUpdateRequestMapper {
    type Src<'a> = KeyUpdateRequestInner;
    type Dst<'a> = KeyUpdateRequest;

    type SrcOwned = KeyUpdateRequestInner;
    type DstOwned = KeyUpdateRequest;
}

pub struct SpecKeyUpdate {
    pub request_update: SpecKeyUpdateRequest,
}
pub type SpecKeyUpdateInner = SpecKeyUpdateRequest;
impl SpecFrom<SpecKeyUpdate> for SpecKeyUpdateInner {
    open spec fn spec_from(m: SpecKeyUpdate) -> SpecKeyUpdateInner {
        m.request_update
    }
}
impl SpecFrom<SpecKeyUpdateInner> for SpecKeyUpdate {
    open spec fn spec_from(m: SpecKeyUpdateInner) -> SpecKeyUpdate {
        let request_update = m;
        SpecKeyUpdate {
            request_update,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyUpdate {
    pub request_update: KeyUpdateRequest,
}
pub type KeyUpdateInner = KeyUpdateRequest;
impl View for KeyUpdate {
    type V = SpecKeyUpdate;
    open spec fn view(&self) -> Self::V {
        SpecKeyUpdate {
            request_update: self.request_update@,
        }
    }
}
impl From<KeyUpdate> for KeyUpdateInner {
    fn ex_from(m: KeyUpdate) -> KeyUpdateInner {
        m.request_update
    }
}
impl From<KeyUpdateInner> for KeyUpdate {
    fn ex_from(m: KeyUpdateInner) -> KeyUpdate {
        let request_update = m;
        KeyUpdate {
            request_update,
        }
    }
}
pub struct KeyUpdateMapper;
impl View for KeyUpdateMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for KeyUpdateMapper {
    type Src = SpecKeyUpdateInner;
    type Dst = SpecKeyUpdate;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for KeyUpdateMapper {
    type Src<'a> = KeyUpdateInner;
    type Dst<'a> = KeyUpdate;
    type SrcOwned = KeyUpdateOwnedInner;
    type DstOwned = KeyUpdateOwned;
}
pub struct KeyUpdateOwned {
    pub request_update: KeyUpdateRequestOwned,
}
pub type KeyUpdateOwnedInner = KeyUpdateRequestOwned;
impl View for KeyUpdateOwned {
    type V = SpecKeyUpdate;
    open spec fn view(&self) -> Self::V {
        SpecKeyUpdate {
            request_update: self.request_update@,
        }
    }
}
impl From<KeyUpdateOwned> for KeyUpdateOwnedInner {
    fn ex_from(m: KeyUpdateOwned) -> KeyUpdateOwnedInner {
        m.request_update
    }
}
impl From<KeyUpdateOwnedInner> for KeyUpdateOwned {
    fn ex_from(m: KeyUpdateOwnedInner) -> KeyUpdateOwned {
        let request_update = m;
        KeyUpdateOwned {
            request_update,
        }
    }
}

pub struct SpecSupportedVersionsServer {
    pub selected_version: SpecProtocolVersion,
}
pub type SpecSupportedVersionsServerInner = SpecProtocolVersion;
impl SpecFrom<SpecSupportedVersionsServer> for SpecSupportedVersionsServerInner {
    open spec fn spec_from(m: SpecSupportedVersionsServer) -> SpecSupportedVersionsServerInner {
        m.selected_version
    }
}
impl SpecFrom<SpecSupportedVersionsServerInner> for SpecSupportedVersionsServer {
    open spec fn spec_from(m: SpecSupportedVersionsServerInner) -> SpecSupportedVersionsServer {
        let selected_version = m;
        SpecSupportedVersionsServer {
            selected_version,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SupportedVersionsServer {
    pub selected_version: ProtocolVersion,
}
pub type SupportedVersionsServerInner = ProtocolVersion;
impl View for SupportedVersionsServer {
    type V = SpecSupportedVersionsServer;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsServer {
            selected_version: self.selected_version@,
        }
    }
}
impl From<SupportedVersionsServer> for SupportedVersionsServerInner {
    fn ex_from(m: SupportedVersionsServer) -> SupportedVersionsServerInner {
        m.selected_version
    }
}
impl From<SupportedVersionsServerInner> for SupportedVersionsServer {
    fn ex_from(m: SupportedVersionsServerInner) -> SupportedVersionsServer {
        let selected_version = m;
        SupportedVersionsServer {
            selected_version,
        }
    }
}
pub struct SupportedVersionsServerMapper;
impl View for SupportedVersionsServerMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SupportedVersionsServerMapper {
    type Src = SpecSupportedVersionsServerInner;
    type Dst = SpecSupportedVersionsServer;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SupportedVersionsServerMapper {
    type Src<'a> = SupportedVersionsServerInner;
    type Dst<'a> = SupportedVersionsServer;
    type SrcOwned = SupportedVersionsServerOwnedInner;
    type DstOwned = SupportedVersionsServerOwned;
}
pub struct SupportedVersionsServerOwned {
    pub selected_version: ProtocolVersionOwned,
}
pub type SupportedVersionsServerOwnedInner = ProtocolVersionOwned;
impl View for SupportedVersionsServerOwned {
    type V = SpecSupportedVersionsServer;
    open spec fn view(&self) -> Self::V {
        SpecSupportedVersionsServer {
            selected_version: self.selected_version@,
        }
    }
}
impl From<SupportedVersionsServerOwned> for SupportedVersionsServerOwnedInner {
    fn ex_from(m: SupportedVersionsServerOwned) -> SupportedVersionsServerOwnedInner {
        m.selected_version
    }
}
impl From<SupportedVersionsServerOwnedInner> for SupportedVersionsServerOwned {
    fn ex_from(m: SupportedVersionsServerOwnedInner) -> SupportedVersionsServerOwned {
        let selected_version = m;
        SupportedVersionsServerOwned {
            selected_version,
        }
    }
}

pub struct SpecOpaque1Ffffff {
    pub l: u24,
    pub data: Seq<u8>,
}
pub type SpecOpaque1FfffffInner = (u24, Seq<u8>);
impl SpecFrom<SpecOpaque1Ffffff> for SpecOpaque1FfffffInner {
    open spec fn spec_from(m: SpecOpaque1Ffffff) -> SpecOpaque1FfffffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque1FfffffInner> for SpecOpaque1Ffffff {
    open spec fn spec_from(m: SpecOpaque1FfffffInner) -> SpecOpaque1Ffffff {
        let (l, data) = m;
        SpecOpaque1Ffffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque1Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}
pub type Opaque1FfffffInner<'a> = (u24, &'a [u8]);
impl View for Opaque1Ffffff<'_> {
    type V = SpecOpaque1Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque1Ffffff<'a>> for Opaque1FfffffInner<'a> {
    fn ex_from(m: Opaque1Ffffff<'a>) -> Opaque1FfffffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque1FfffffInner<'a>> for Opaque1Ffffff<'a> {
    fn ex_from(m: Opaque1FfffffInner<'a>) -> Opaque1Ffffff<'a> {
        let (l, data) = m;
        Opaque1Ffffff {
            l,
            data,
        }
    }
}
pub struct Opaque1FfffffMapper;
impl View for Opaque1FfffffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque1FfffffMapper {
    type Src = SpecOpaque1FfffffInner;
    type Dst = SpecOpaque1Ffffff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque1FfffffMapper {
    type Src<'a> = Opaque1FfffffInner<'a>;
    type Dst<'a> = Opaque1Ffffff<'a>;
    type SrcOwned = Opaque1FfffffOwnedInner;
    type DstOwned = Opaque1FfffffOwned;
}
pub struct Opaque1FfffffOwned {
    pub l: u24,
    pub data: Vec<u8>,
}
pub type Opaque1FfffffOwnedInner = (u24, Vec<u8>);
impl View for Opaque1FfffffOwned {
    type V = SpecOpaque1Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque1Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque1FfffffOwned> for Opaque1FfffffOwnedInner {
    fn ex_from(m: Opaque1FfffffOwned) -> Opaque1FfffffOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque1FfffffOwnedInner> for Opaque1FfffffOwned {
    fn ex_from(m: Opaque1FfffffOwnedInner) -> Opaque1FfffffOwned {
        let (l, data) = m;
        Opaque1FfffffOwned {
            l,
            data,
        }
    }
}

pub type SpecEncryptedExtensionsExtensions = Seq<SpecExtension>;
pub type EncryptedExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;
pub type EncryptedExtensionsExtensionsOwned = RepeatResult<ExtensionOwned>;

pub struct SpecEncryptedExtensions {
    pub l: SpecUint0Ffff,
    pub extensions: SpecEncryptedExtensionsExtensions,
}
pub type SpecEncryptedExtensionsInner = (SpecUint0Ffff, SpecEncryptedExtensionsExtensions);
impl SpecFrom<SpecEncryptedExtensions> for SpecEncryptedExtensionsInner {
    open spec fn spec_from(m: SpecEncryptedExtensions) -> SpecEncryptedExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecEncryptedExtensionsInner> for SpecEncryptedExtensions {
    open spec fn spec_from(m: SpecEncryptedExtensionsInner) -> SpecEncryptedExtensions {
        let (l, extensions) = m;
        SpecEncryptedExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EncryptedExtensions<'a> {
    pub l: Uint0Ffff,
    pub extensions: EncryptedExtensionsExtensions<'a>,
}
pub type EncryptedExtensionsInner<'a> = (Uint0Ffff, EncryptedExtensionsExtensions<'a>);
impl View for EncryptedExtensions<'_> {
    type V = SpecEncryptedExtensions;
    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<EncryptedExtensions<'a>> for EncryptedExtensionsInner<'a> {
    fn ex_from(m: EncryptedExtensions<'a>) -> EncryptedExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<EncryptedExtensionsInner<'a>> for EncryptedExtensions<'a> {
    fn ex_from(m: EncryptedExtensionsInner<'a>) -> EncryptedExtensions<'a> {
        let (l, extensions) = m;
        EncryptedExtensions {
            l,
            extensions,
        }
    }
}
pub struct EncryptedExtensionsMapper;
impl View for EncryptedExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EncryptedExtensionsMapper {
    type Src = SpecEncryptedExtensionsInner;
    type Dst = SpecEncryptedExtensions;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for EncryptedExtensionsMapper {
    type Src<'a> = EncryptedExtensionsInner<'a>;
    type Dst<'a> = EncryptedExtensions<'a>;
    type SrcOwned = EncryptedExtensionsOwnedInner;
    type DstOwned = EncryptedExtensionsOwned;
}
pub struct EncryptedExtensionsOwned {
    pub l: Uint0FfffOwned,
    pub extensions: EncryptedExtensionsExtensionsOwned,
}
pub type EncryptedExtensionsOwnedInner = (Uint0FfffOwned, EncryptedExtensionsExtensionsOwned);
impl View for EncryptedExtensionsOwned {
    type V = SpecEncryptedExtensions;
    open spec fn view(&self) -> Self::V {
        SpecEncryptedExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl From<EncryptedExtensionsOwned> for EncryptedExtensionsOwnedInner {
    fn ex_from(m: EncryptedExtensionsOwned) -> EncryptedExtensionsOwnedInner {
        (m.l, m.extensions)
    }
}
impl From<EncryptedExtensionsOwnedInner> for EncryptedExtensionsOwned {
    fn ex_from(m: EncryptedExtensionsOwnedInner) -> EncryptedExtensionsOwned {
        let (l, extensions) = m;
        EncryptedExtensionsOwned {
            l,
            extensions,
        }
    }
}

pub type SpecCertificateExtensions = SpecEncryptedExtensions;
pub type CertificateExtensions<'a> = EncryptedExtensions<'a>;
pub type CertificateExtensionsOwned = EncryptedExtensionsOwned;

pub struct SpecCertificateEntry {
    pub cert_data: SpecOpaque1Ffffff,
    pub extensions: SpecCertificateExtensions,
}
pub type SpecCertificateEntryInner = (SpecOpaque1Ffffff, SpecCertificateExtensions);
impl SpecFrom<SpecCertificateEntry> for SpecCertificateEntryInner {
    open spec fn spec_from(m: SpecCertificateEntry) -> SpecCertificateEntryInner {
        (m.cert_data, m.extensions)
    }
}
impl SpecFrom<SpecCertificateEntryInner> for SpecCertificateEntry {
    open spec fn spec_from(m: SpecCertificateEntryInner) -> SpecCertificateEntry {
        let (cert_data, extensions) = m;
        SpecCertificateEntry {
            cert_data,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateEntry<'a> {
    pub cert_data: Opaque1Ffffff<'a>,
    pub extensions: CertificateExtensions<'a>,
}
pub type CertificateEntryInner<'a> = (Opaque1Ffffff<'a>, CertificateExtensions<'a>);
impl View for CertificateEntry<'_> {
    type V = SpecCertificateEntry;
    open spec fn view(&self) -> Self::V {
        SpecCertificateEntry {
            cert_data: self.cert_data@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateEntry<'a>> for CertificateEntryInner<'a> {
    fn ex_from(m: CertificateEntry<'a>) -> CertificateEntryInner<'a> {
        (m.cert_data, m.extensions)
    }
}
impl<'a> From<CertificateEntryInner<'a>> for CertificateEntry<'a> {
    fn ex_from(m: CertificateEntryInner<'a>) -> CertificateEntry<'a> {
        let (cert_data, extensions) = m;
        CertificateEntry {
            cert_data,
            extensions,
        }
    }
}
pub struct CertificateEntryMapper;
impl View for CertificateEntryMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateEntryMapper {
    type Src = SpecCertificateEntryInner;
    type Dst = SpecCertificateEntry;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateEntryMapper {
    type Src<'a> = CertificateEntryInner<'a>;
    type Dst<'a> = CertificateEntry<'a>;
    type SrcOwned = CertificateEntryOwnedInner;
    type DstOwned = CertificateEntryOwned;
}
pub struct CertificateEntryOwned {
    pub cert_data: Opaque1FfffffOwned,
    pub extensions: CertificateExtensionsOwned,
}
pub type CertificateEntryOwnedInner = (Opaque1FfffffOwned, CertificateExtensionsOwned);
impl View for CertificateEntryOwned {
    type V = SpecCertificateEntry;
    open spec fn view(&self) -> Self::V {
        SpecCertificateEntry {
            cert_data: self.cert_data@,
            extensions: self.extensions@,
        }
    }
}
impl From<CertificateEntryOwned> for CertificateEntryOwnedInner {
    fn ex_from(m: CertificateEntryOwned) -> CertificateEntryOwnedInner {
        (m.cert_data, m.extensions)
    }
}
impl From<CertificateEntryOwnedInner> for CertificateEntryOwned {
    fn ex_from(m: CertificateEntryOwnedInner) -> CertificateEntryOwned {
        let (cert_data, extensions) = m;
        CertificateEntryOwned {
            cert_data,
            extensions,
        }
    }
}

pub type SpecCertificateListList = Seq<SpecCertificateEntry>;
pub type CertificateListList<'a> = RepeatResult<CertificateEntry<'a>>;
pub type CertificateListListOwned = RepeatResult<CertificateEntryOwned>;

pub struct SpecCertificateList {
    pub l: u24,
    pub list: SpecCertificateListList,
}
pub type SpecCertificateListInner = (u24, SpecCertificateListList);
impl SpecFrom<SpecCertificateList> for SpecCertificateListInner {
    open spec fn spec_from(m: SpecCertificateList) -> SpecCertificateListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecCertificateListInner> for SpecCertificateList {
    open spec fn spec_from(m: SpecCertificateListInner) -> SpecCertificateList {
        let (l, list) = m;
        SpecCertificateList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateList<'a> {
    pub l: u24,
    pub list: CertificateListList<'a>,
}
pub type CertificateListInner<'a> = (u24, CertificateListList<'a>);
impl View for CertificateList<'_> {
    type V = SpecCertificateList;
    open spec fn view(&self) -> Self::V {
        SpecCertificateList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl<'a> From<CertificateList<'a>> for CertificateListInner<'a> {
    fn ex_from(m: CertificateList<'a>) -> CertificateListInner<'a> {
        (m.l, m.list)
    }
}
impl<'a> From<CertificateListInner<'a>> for CertificateList<'a> {
    fn ex_from(m: CertificateListInner<'a>) -> CertificateList<'a> {
        let (l, list) = m;
        CertificateList {
            l,
            list,
        }
    }
}
pub struct CertificateListMapper;
impl View for CertificateListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateListMapper {
    type Src = SpecCertificateListInner;
    type Dst = SpecCertificateList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateListMapper {
    type Src<'a> = CertificateListInner<'a>;
    type Dst<'a> = CertificateList<'a>;
    type SrcOwned = CertificateListOwnedInner;
    type DstOwned = CertificateListOwned;
}
pub struct CertificateListOwned {
    pub l: u24,
    pub list: CertificateListListOwned,
}
pub type CertificateListOwnedInner = (u24, CertificateListListOwned);
impl View for CertificateListOwned {
    type V = SpecCertificateList;
    open spec fn view(&self) -> Self::V {
        SpecCertificateList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<CertificateListOwned> for CertificateListOwnedInner {
    fn ex_from(m: CertificateListOwned) -> CertificateListOwnedInner {
        (m.l, m.list)
    }
}
impl From<CertificateListOwnedInner> for CertificateListOwned {
    fn ex_from(m: CertificateListOwnedInner) -> CertificateListOwned {
        let (l, list) = m;
        CertificateListOwned {
            l,
            list,
        }
    }
}

pub struct SpecCertificate {
    pub certificate_request_context: SpecOpaque0Ff,
    pub certificate_list: SpecCertificateList,
}
pub type SpecCertificateInner = (SpecOpaque0Ff, SpecCertificateList);
impl SpecFrom<SpecCertificate> for SpecCertificateInner {
    open spec fn spec_from(m: SpecCertificate) -> SpecCertificateInner {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl SpecFrom<SpecCertificateInner> for SpecCertificate {
    open spec fn spec_from(m: SpecCertificateInner) -> SpecCertificate {
        let (certificate_request_context, certificate_list) = m;
        SpecCertificate {
            certificate_request_context,
            certificate_list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Certificate<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub certificate_list: CertificateList<'a>,
}
pub type CertificateInner<'a> = (Opaque0Ff<'a>, CertificateList<'a>);
impl View for Certificate<'_> {
    type V = SpecCertificate;
    open spec fn view(&self) -> Self::V {
        SpecCertificate {
            certificate_request_context: self.certificate_request_context@,
            certificate_list: self.certificate_list@,
        }
    }
}
impl<'a> From<Certificate<'a>> for CertificateInner<'a> {
    fn ex_from(m: Certificate<'a>) -> CertificateInner<'a> {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl<'a> From<CertificateInner<'a>> for Certificate<'a> {
    fn ex_from(m: CertificateInner<'a>) -> Certificate<'a> {
        let (certificate_request_context, certificate_list) = m;
        Certificate {
            certificate_request_context,
            certificate_list,
        }
    }
}
pub struct CertificateMapper;
impl View for CertificateMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateMapper {
    type Src = SpecCertificateInner;
    type Dst = SpecCertificate;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateMapper {
    type Src<'a> = CertificateInner<'a>;
    type Dst<'a> = Certificate<'a>;
    type SrcOwned = CertificateOwnedInner;
    type DstOwned = CertificateOwned;
}
pub struct CertificateOwned {
    pub certificate_request_context: Opaque0FfOwned,
    pub certificate_list: CertificateListOwned,
}
pub type CertificateOwnedInner = (Opaque0FfOwned, CertificateListOwned);
impl View for CertificateOwned {
    type V = SpecCertificate;
    open spec fn view(&self) -> Self::V {
        SpecCertificate {
            certificate_request_context: self.certificate_request_context@,
            certificate_list: self.certificate_list@,
        }
    }
}
impl From<CertificateOwned> for CertificateOwnedInner {
    fn ex_from(m: CertificateOwned) -> CertificateOwnedInner {
        (m.certificate_request_context, m.certificate_list)
    }
}
impl From<CertificateOwnedInner> for CertificateOwned {
    fn ex_from(m: CertificateOwnedInner) -> CertificateOwned {
        let (certificate_request_context, certificate_list) = m;
        CertificateOwned {
            certificate_request_context,
            certificate_list,
        }
    }
}

pub struct SpecEarlyDataIndicationNewSessionTicket {
    pub max_early_data_size: u32,
}
pub type SpecEarlyDataIndicationNewSessionTicketInner = u32;
impl SpecFrom<SpecEarlyDataIndicationNewSessionTicket> for SpecEarlyDataIndicationNewSessionTicketInner {
    open spec fn spec_from(m: SpecEarlyDataIndicationNewSessionTicket) -> SpecEarlyDataIndicationNewSessionTicketInner {
        m.max_early_data_size
    }
}
impl SpecFrom<SpecEarlyDataIndicationNewSessionTicketInner> for SpecEarlyDataIndicationNewSessionTicket {
    open spec fn spec_from(m: SpecEarlyDataIndicationNewSessionTicketInner) -> SpecEarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EarlyDataIndicationNewSessionTicket {
    pub max_early_data_size: u32,
}
pub type EarlyDataIndicationNewSessionTicketInner = u32;
impl View for EarlyDataIndicationNewSessionTicket {
    type V = SpecEarlyDataIndicationNewSessionTicket;
    open spec fn view(&self) -> Self::V {
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size: self.max_early_data_size@,
        }
    }
}
impl From<EarlyDataIndicationNewSessionTicket> for EarlyDataIndicationNewSessionTicketInner {
    fn ex_from(m: EarlyDataIndicationNewSessionTicket) -> EarlyDataIndicationNewSessionTicketInner {
        m.max_early_data_size
    }
}
impl From<EarlyDataIndicationNewSessionTicketInner> for EarlyDataIndicationNewSessionTicket {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketInner) -> EarlyDataIndicationNewSessionTicket {
        let max_early_data_size = m;
        EarlyDataIndicationNewSessionTicket {
            max_early_data_size,
        }
    }
}
pub struct EarlyDataIndicationNewSessionTicketMapper;
impl View for EarlyDataIndicationNewSessionTicketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for EarlyDataIndicationNewSessionTicketMapper {
    type Src = SpecEarlyDataIndicationNewSessionTicketInner;
    type Dst = SpecEarlyDataIndicationNewSessionTicket;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for EarlyDataIndicationNewSessionTicketMapper {
    type Src<'a> = EarlyDataIndicationNewSessionTicketInner;
    type Dst<'a> = EarlyDataIndicationNewSessionTicket;
    type SrcOwned = EarlyDataIndicationNewSessionTicketOwnedInner;
    type DstOwned = EarlyDataIndicationNewSessionTicketOwned;
}
pub struct EarlyDataIndicationNewSessionTicketOwned {
    pub max_early_data_size: u32,
}
pub type EarlyDataIndicationNewSessionTicketOwnedInner = u32;
impl View for EarlyDataIndicationNewSessionTicketOwned {
    type V = SpecEarlyDataIndicationNewSessionTicket;
    open spec fn view(&self) -> Self::V {
        SpecEarlyDataIndicationNewSessionTicket {
            max_early_data_size: self.max_early_data_size@,
        }
    }
}
impl From<EarlyDataIndicationNewSessionTicketOwned> for EarlyDataIndicationNewSessionTicketOwnedInner {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketOwned) -> EarlyDataIndicationNewSessionTicketOwnedInner {
        m.max_early_data_size
    }
}
impl From<EarlyDataIndicationNewSessionTicketOwnedInner> for EarlyDataIndicationNewSessionTicketOwned {
    fn ex_from(m: EarlyDataIndicationNewSessionTicketOwnedInner) -> EarlyDataIndicationNewSessionTicketOwned {
        let max_early_data_size = m;
        EarlyDataIndicationNewSessionTicketOwned {
            max_early_data_size,
        }
    }
}

pub struct SpecPreSharedKeyServerExtension {
    pub selected_identity: u16,
}
pub type SpecPreSharedKeyServerExtensionInner = u16;
impl SpecFrom<SpecPreSharedKeyServerExtension> for SpecPreSharedKeyServerExtensionInner {
    open spec fn spec_from(m: SpecPreSharedKeyServerExtension) -> SpecPreSharedKeyServerExtensionInner {
        m.selected_identity
    }
}
impl SpecFrom<SpecPreSharedKeyServerExtensionInner> for SpecPreSharedKeyServerExtension {
    open spec fn spec_from(m: SpecPreSharedKeyServerExtensionInner) -> SpecPreSharedKeyServerExtension {
        let selected_identity = m;
        SpecPreSharedKeyServerExtension {
            selected_identity,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreSharedKeyServerExtension {
    pub selected_identity: u16,
}
pub type PreSharedKeyServerExtensionInner = u16;
impl View for PreSharedKeyServerExtension {
    type V = SpecPreSharedKeyServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyServerExtension {
            selected_identity: self.selected_identity@,
        }
    }
}
impl From<PreSharedKeyServerExtension> for PreSharedKeyServerExtensionInner {
    fn ex_from(m: PreSharedKeyServerExtension) -> PreSharedKeyServerExtensionInner {
        m.selected_identity
    }
}
impl From<PreSharedKeyServerExtensionInner> for PreSharedKeyServerExtension {
    fn ex_from(m: PreSharedKeyServerExtensionInner) -> PreSharedKeyServerExtension {
        let selected_identity = m;
        PreSharedKeyServerExtension {
            selected_identity,
        }
    }
}
pub struct PreSharedKeyServerExtensionMapper;
impl View for PreSharedKeyServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for PreSharedKeyServerExtensionMapper {
    type Src = SpecPreSharedKeyServerExtensionInner;
    type Dst = SpecPreSharedKeyServerExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for PreSharedKeyServerExtensionMapper {
    type Src<'a> = PreSharedKeyServerExtensionInner;
    type Dst<'a> = PreSharedKeyServerExtension;
    type SrcOwned = PreSharedKeyServerExtensionOwnedInner;
    type DstOwned = PreSharedKeyServerExtensionOwned;
}
pub struct PreSharedKeyServerExtensionOwned {
    pub selected_identity: u16,
}
pub type PreSharedKeyServerExtensionOwnedInner = u16;
impl View for PreSharedKeyServerExtensionOwned {
    type V = SpecPreSharedKeyServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecPreSharedKeyServerExtension {
            selected_identity: self.selected_identity@,
        }
    }
}
impl From<PreSharedKeyServerExtensionOwned> for PreSharedKeyServerExtensionOwnedInner {
    fn ex_from(m: PreSharedKeyServerExtensionOwned) -> PreSharedKeyServerExtensionOwnedInner {
        m.selected_identity
    }
}
impl From<PreSharedKeyServerExtensionOwnedInner> for PreSharedKeyServerExtensionOwned {
    fn ex_from(m: PreSharedKeyServerExtensionOwnedInner) -> PreSharedKeyServerExtensionOwned {
        let selected_identity = m;
        PreSharedKeyServerExtensionOwned {
            selected_identity,
        }
    }
}

pub type SpecRandom = Seq<u8>;
pub type Random<'a> = &'a [u8];
pub type RandomOwned = Vec<u8>;

pub struct SpecSessionId {
    pub l: u8,
    pub id: Seq<u8>,
}
pub type SpecSessionIdInner = (u8, Seq<u8>);
impl SpecFrom<SpecSessionId> for SpecSessionIdInner {
    open spec fn spec_from(m: SpecSessionId) -> SpecSessionIdInner {
        (m.l, m.id)
    }
}
impl SpecFrom<SpecSessionIdInner> for SpecSessionId {
    open spec fn spec_from(m: SpecSessionIdInner) -> SpecSessionId {
        let (l, id) = m;
        SpecSessionId {
            l,
            id,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SessionId<'a> {
    pub l: u8,
    pub id: &'a [u8],
}
pub type SessionIdInner<'a> = (u8, &'a [u8]);
impl View for SessionId<'_> {
    type V = SpecSessionId;
    open spec fn view(&self) -> Self::V {
        SpecSessionId {
            l: self.l@,
            id: self.id@,
        }
    }
}
impl<'a> From<SessionId<'a>> for SessionIdInner<'a> {
    fn ex_from(m: SessionId<'a>) -> SessionIdInner<'a> {
        (m.l, m.id)
    }
}
impl<'a> From<SessionIdInner<'a>> for SessionId<'a> {
    fn ex_from(m: SessionIdInner<'a>) -> SessionId<'a> {
        let (l, id) = m;
        SessionId {
            l,
            id,
        }
    }
}
pub struct SessionIdMapper;
impl View for SessionIdMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SessionIdMapper {
    type Src = SpecSessionIdInner;
    type Dst = SpecSessionId;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SessionIdMapper {
    type Src<'a> = SessionIdInner<'a>;
    type Dst<'a> = SessionId<'a>;
    type SrcOwned = SessionIdOwnedInner;
    type DstOwned = SessionIdOwned;
}
pub struct SessionIdOwned {
    pub l: u8,
    pub id: Vec<u8>,
}
pub type SessionIdOwnedInner = (u8, Vec<u8>);
impl View for SessionIdOwned {
    type V = SpecSessionId;
    open spec fn view(&self) -> Self::V {
        SpecSessionId {
            l: self.l@,
            id: self.id@,
        }
    }
}
impl From<SessionIdOwned> for SessionIdOwnedInner {
    fn ex_from(m: SessionIdOwned) -> SessionIdOwnedInner {
        (m.l, m.id)
    }
}
impl From<SessionIdOwnedInner> for SessionIdOwned {
    fn ex_from(m: SessionIdOwnedInner) -> SessionIdOwned {
        let (l, id) = m;
        SessionIdOwned {
            l,
            id,
        }
    }
}

pub type SpecCipherSuite = u16;
pub type CipherSuite = u16;
pub type CipherSuiteOwned = u16;

pub type SpecCipherSuiteListList = Seq<SpecCipherSuite>;
pub type CipherSuiteListList = RepeatResult<CipherSuite>;
pub type CipherSuiteListListOwned = RepeatResult<CipherSuiteOwned>;

pub struct SpecCipherSuiteList {
    pub l: SpecUint2Fffe,
    pub list: SpecCipherSuiteListList,
}
pub type SpecCipherSuiteListInner = (SpecUint2Fffe, SpecCipherSuiteListList);
impl SpecFrom<SpecCipherSuiteList> for SpecCipherSuiteListInner {
    open spec fn spec_from(m: SpecCipherSuiteList) -> SpecCipherSuiteListInner {
        (m.l, m.list)
    }
}
impl SpecFrom<SpecCipherSuiteListInner> for SpecCipherSuiteList {
    open spec fn spec_from(m: SpecCipherSuiteListInner) -> SpecCipherSuiteList {
        let (l, list) = m;
        SpecCipherSuiteList {
            l,
            list,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CipherSuiteList {
    pub l: Uint2Fffe,
    pub list: CipherSuiteListList,
}
pub type CipherSuiteListInner = (Uint2Fffe, CipherSuiteListList);
impl View for CipherSuiteList {
    type V = SpecCipherSuiteList;
    open spec fn view(&self) -> Self::V {
        SpecCipherSuiteList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<CipherSuiteList> for CipherSuiteListInner {
    fn ex_from(m: CipherSuiteList) -> CipherSuiteListInner {
        (m.l, m.list)
    }
}
impl From<CipherSuiteListInner> for CipherSuiteList {
    fn ex_from(m: CipherSuiteListInner) -> CipherSuiteList {
        let (l, list) = m;
        CipherSuiteList {
            l,
            list,
        }
    }
}
pub struct CipherSuiteListMapper;
impl View for CipherSuiteListMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CipherSuiteListMapper {
    type Src = SpecCipherSuiteListInner;
    type Dst = SpecCipherSuiteList;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CipherSuiteListMapper {
    type Src<'a> = CipherSuiteListInner;
    type Dst<'a> = CipherSuiteList;
    type SrcOwned = CipherSuiteListOwnedInner;
    type DstOwned = CipherSuiteListOwned;
}
pub struct CipherSuiteListOwned {
    pub l: Uint2FffeOwned,
    pub list: CipherSuiteListListOwned,
}
pub type CipherSuiteListOwnedInner = (Uint2FffeOwned, CipherSuiteListListOwned);
impl View for CipherSuiteListOwned {
    type V = SpecCipherSuiteList;
    open spec fn view(&self) -> Self::V {
        SpecCipherSuiteList {
            l: self.l@,
            list: self.list@,
        }
    }
}
impl From<CipherSuiteListOwned> for CipherSuiteListOwnedInner {
    fn ex_from(m: CipherSuiteListOwned) -> CipherSuiteListOwnedInner {
        (m.l, m.list)
    }
}
impl From<CipherSuiteListOwnedInner> for CipherSuiteListOwned {
    fn ex_from(m: CipherSuiteListOwnedInner) -> CipherSuiteListOwned {
        let (l, list) = m;
        CipherSuiteListOwned {
            l,
            list,
        }
    }
}

pub struct SpecClientHelloExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecClientHelloExtensionExtensionData,
}
pub type SpecClientHelloExtensionInner = ((SpecExtensionType, u16), SpecClientHelloExtensionExtensionData);
impl SpecFrom<SpecClientHelloExtension> for SpecClientHelloExtensionInner {
    open spec fn spec_from(m: SpecClientHelloExtension) -> SpecClientHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecClientHelloExtensionInner> for SpecClientHelloExtension {
    open spec fn spec_from(m: SpecClientHelloExtensionInner) -> SpecClientHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecClientHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: ClientHelloExtensionExtensionData<'a>,
}
pub type ClientHelloExtensionInner<'a> = ((ExtensionType, u16), ClientHelloExtensionExtensionData<'a>);
impl View for ClientHelloExtension<'_> {
    type V = SpecClientHelloExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
impl<'a> From<ClientHelloExtension<'a>> for ClientHelloExtensionInner<'a> {
    fn ex_from(m: ClientHelloExtension<'a>) -> ClientHelloExtensionInner<'a> {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<ClientHelloExtensionInner<'a>> for ClientHelloExtension<'a> {
    fn ex_from(m: ClientHelloExtensionInner<'a>) -> ClientHelloExtension<'a> {
        let ((extension_type, ext_len), extension_data) = m;
        ClientHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
pub struct ClientHelloExtensionMapper;
impl View for ClientHelloExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloExtensionMapper {
    type Src = SpecClientHelloExtensionInner;
    type Dst = SpecClientHelloExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientHelloExtensionMapper {
    type Src<'a> = ClientHelloExtensionInner<'a>;
    type Dst<'a> = ClientHelloExtension<'a>;
    type SrcOwned = ClientHelloExtensionOwnedInner;
    type DstOwned = ClientHelloExtensionOwned;
}
pub struct ClientHelloExtensionOwned {
    pub extension_type: ExtensionTypeOwned,
    pub ext_len: u16,
    pub extension_data: ClientHelloExtensionExtensionDataOwned,
}
pub type ClientHelloExtensionOwnedInner = ((ExtensionTypeOwned, u16), ClientHelloExtensionExtensionDataOwned);
impl View for ClientHelloExtensionOwned {
    type V = SpecClientHelloExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
impl From<ClientHelloExtensionOwned> for ClientHelloExtensionOwnedInner {
    fn ex_from(m: ClientHelloExtensionOwned) -> ClientHelloExtensionOwnedInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl From<ClientHelloExtensionOwnedInner> for ClientHelloExtensionOwned {
    fn ex_from(m: ClientHelloExtensionOwnedInner) -> ClientHelloExtensionOwned {
        let ((extension_type, ext_len), extension_data) = m;
        ClientHelloExtensionOwned {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}

pub type SpecClientExtensionsExtensions = Seq<SpecClientHelloExtension>;
pub type ClientExtensionsExtensions<'a> = RepeatResult<ClientHelloExtension<'a>>;
pub type ClientExtensionsExtensionsOwned = RepeatResult<ClientHelloExtensionOwned>;

pub struct SpecClientExtensions {
    pub l: u16,
    pub extensions: SpecClientExtensionsExtensions,
}
pub type SpecClientExtensionsInner = (u16, SpecClientExtensionsExtensions);
impl SpecFrom<SpecClientExtensions> for SpecClientExtensionsInner {
    open spec fn spec_from(m: SpecClientExtensions) -> SpecClientExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecClientExtensionsInner> for SpecClientExtensions {
    open spec fn spec_from(m: SpecClientExtensionsInner) -> SpecClientExtensions {
        let (l, extensions) = m;
        SpecClientExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientExtensions<'a> {
    pub l: u16,
    pub extensions: ClientExtensionsExtensions<'a>,
}
pub type ClientExtensionsInner<'a> = (u16, ClientExtensionsExtensions<'a>);
impl View for ClientExtensions<'_> {
    type V = SpecClientExtensions;
    open spec fn view(&self) -> Self::V {
        SpecClientExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ClientExtensions<'a>> for ClientExtensionsInner<'a> {
    fn ex_from(m: ClientExtensions<'a>) -> ClientExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<ClientExtensionsInner<'a>> for ClientExtensions<'a> {
    fn ex_from(m: ClientExtensionsInner<'a>) -> ClientExtensions<'a> {
        let (l, extensions) = m;
        ClientExtensions {
            l,
            extensions,
        }
    }
}
pub struct ClientExtensionsMapper;
impl View for ClientExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientExtensionsMapper {
    type Src = SpecClientExtensionsInner;
    type Dst = SpecClientExtensions;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientExtensionsMapper {
    type Src<'a> = ClientExtensionsInner<'a>;
    type Dst<'a> = ClientExtensions<'a>;
    type SrcOwned = ClientExtensionsOwnedInner;
    type DstOwned = ClientExtensionsOwned;
}
pub struct ClientExtensionsOwned {
    pub l: u16,
    pub extensions: ClientExtensionsExtensionsOwned,
}
pub type ClientExtensionsOwnedInner = (u16, ClientExtensionsExtensionsOwned);
impl View for ClientExtensionsOwned {
    type V = SpecClientExtensions;
    open spec fn view(&self) -> Self::V {
        SpecClientExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl From<ClientExtensionsOwned> for ClientExtensionsOwnedInner {
    fn ex_from(m: ClientExtensionsOwned) -> ClientExtensionsOwnedInner {
        (m.l, m.extensions)
    }
}
impl From<ClientExtensionsOwnedInner> for ClientExtensionsOwned {
    fn ex_from(m: ClientExtensionsOwnedInner) -> ClientExtensionsOwned {
        let (l, extensions) = m;
        ClientExtensionsOwned {
            l,
            extensions,
        }
    }
}

pub struct SpecClientHello {
    pub legacy_version: SpecProtocolVersion,
    pub random: SpecRandom,
    pub legacy_session_id: SpecSessionId,
    pub cipher_suites: SpecCipherSuiteList,
    pub legacy_compression_methods: SpecOpaque1Ff,
    pub extensions: SpecClientExtensions,
}
pub type SpecClientHelloInner = (SpecProtocolVersion, (SpecRandom, (SpecSessionId, (SpecCipherSuiteList, (SpecOpaque1Ff, SpecClientExtensions)))));
impl SpecFrom<SpecClientHello> for SpecClientHelloInner {
    open spec fn spec_from(m: SpecClientHello) -> SpecClientHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl SpecFrom<SpecClientHelloInner> for SpecClientHello {
    open spec fn spec_from(m: SpecClientHelloInner) -> SpecClientHello {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        SpecClientHello {
            legacy_version,
            random,
            legacy_session_id,
            cipher_suites,
            legacy_compression_methods,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientHello<'a> {
    pub legacy_version: ProtocolVersion,
    pub random: Random<'a>,
    pub legacy_session_id: SessionId<'a>,
    pub cipher_suites: CipherSuiteList,
    pub legacy_compression_methods: Opaque1Ff<'a>,
    pub extensions: ClientExtensions<'a>,
}
pub type ClientHelloInner<'a> = (ProtocolVersion, (Random<'a>, (SessionId<'a>, (CipherSuiteList, (Opaque1Ff<'a>, ClientExtensions<'a>)))));
impl View for ClientHello<'_> {
    type V = SpecClientHello;
    open spec fn view(&self) -> Self::V {
        SpecClientHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id: self.legacy_session_id@,
            cipher_suites: self.cipher_suites@,
            legacy_compression_methods: self.legacy_compression_methods@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ClientHello<'a>> for ClientHelloInner<'a> {
    fn ex_from(m: ClientHello<'a>) -> ClientHelloInner<'a> {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl<'a> From<ClientHelloInner<'a>> for ClientHello<'a> {
    fn ex_from(m: ClientHelloInner<'a>) -> ClientHello<'a> {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        ClientHello {
            legacy_version,
            random,
            legacy_session_id,
            cipher_suites,
            legacy_compression_methods,
            extensions,
        }
    }
}
pub struct ClientHelloMapper;
impl View for ClientHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientHelloMapper {
    type Src = SpecClientHelloInner;
    type Dst = SpecClientHello;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientHelloMapper {
    type Src<'a> = ClientHelloInner<'a>;
    type Dst<'a> = ClientHello<'a>;
    type SrcOwned = ClientHelloOwnedInner;
    type DstOwned = ClientHelloOwned;
}
pub struct ClientHelloOwned {
    pub legacy_version: ProtocolVersionOwned,
    pub random: RandomOwned,
    pub legacy_session_id: SessionIdOwned,
    pub cipher_suites: CipherSuiteListOwned,
    pub legacy_compression_methods: Opaque1FfOwned,
    pub extensions: ClientExtensionsOwned,
}
pub type ClientHelloOwnedInner = (ProtocolVersionOwned, (RandomOwned, (SessionIdOwned, (CipherSuiteListOwned, (Opaque1FfOwned, ClientExtensionsOwned)))));
impl View for ClientHelloOwned {
    type V = SpecClientHello;
    open spec fn view(&self) -> Self::V {
        SpecClientHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id: self.legacy_session_id@,
            cipher_suites: self.cipher_suites@,
            legacy_compression_methods: self.legacy_compression_methods@,
            extensions: self.extensions@,
        }
    }
}
impl From<ClientHelloOwned> for ClientHelloOwnedInner {
    fn ex_from(m: ClientHelloOwned) -> ClientHelloOwnedInner {
        (m.legacy_version, (m.random, (m.legacy_session_id, (m.cipher_suites, (m.legacy_compression_methods, m.extensions)))))
    }
}
impl From<ClientHelloOwnedInner> for ClientHelloOwned {
    fn ex_from(m: ClientHelloOwnedInner) -> ClientHelloOwned {
        let (legacy_version, (random, (legacy_session_id, (cipher_suites, (legacy_compression_methods, extensions))))) = m;
        ClientHelloOwned {
            legacy_version,
            random,
            legacy_session_id,
            cipher_suites,
            legacy_compression_methods,
            extensions,
        }
    }
}

pub type SpecCertificateRequestExtensionsExtensions = Seq<SpecExtension>;
pub type CertificateRequestExtensionsExtensions<'a> = RepeatResult<Extension<'a>>;
pub type CertificateRequestExtensionsExtensionsOwned = RepeatResult<ExtensionOwned>;

pub struct SpecCertificateRequestExtensions {
    pub l: SpecUint2Ffff,
    pub extensions: SpecCertificateRequestExtensionsExtensions,
}
pub type SpecCertificateRequestExtensionsInner = (SpecUint2Ffff, SpecCertificateRequestExtensionsExtensions);
impl SpecFrom<SpecCertificateRequestExtensions> for SpecCertificateRequestExtensionsInner {
    open spec fn spec_from(m: SpecCertificateRequestExtensions) -> SpecCertificateRequestExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecCertificateRequestExtensionsInner> for SpecCertificateRequestExtensions {
    open spec fn spec_from(m: SpecCertificateRequestExtensionsInner) -> SpecCertificateRequestExtensions {
        let (l, extensions) = m;
        SpecCertificateRequestExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateRequestExtensions<'a> {
    pub l: Uint2Ffff,
    pub extensions: CertificateRequestExtensionsExtensions<'a>,
}
pub type CertificateRequestExtensionsInner<'a> = (Uint2Ffff, CertificateRequestExtensionsExtensions<'a>);
impl View for CertificateRequestExtensions<'_> {
    type V = SpecCertificateRequestExtensions;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateRequestExtensions<'a>> for CertificateRequestExtensionsInner<'a> {
    fn ex_from(m: CertificateRequestExtensions<'a>) -> CertificateRequestExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<CertificateRequestExtensionsInner<'a>> for CertificateRequestExtensions<'a> {
    fn ex_from(m: CertificateRequestExtensionsInner<'a>) -> CertificateRequestExtensions<'a> {
        let (l, extensions) = m;
        CertificateRequestExtensions {
            l,
            extensions,
        }
    }
}
pub struct CertificateRequestExtensionsMapper;
impl View for CertificateRequestExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestExtensionsMapper {
    type Src = SpecCertificateRequestExtensionsInner;
    type Dst = SpecCertificateRequestExtensions;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateRequestExtensionsMapper {
    type Src<'a> = CertificateRequestExtensionsInner<'a>;
    type Dst<'a> = CertificateRequestExtensions<'a>;
    type SrcOwned = CertificateRequestExtensionsOwnedInner;
    type DstOwned = CertificateRequestExtensionsOwned;
}
pub struct CertificateRequestExtensionsOwned {
    pub l: Uint2FfffOwned,
    pub extensions: CertificateRequestExtensionsExtensionsOwned,
}
pub type CertificateRequestExtensionsOwnedInner = (Uint2FfffOwned, CertificateRequestExtensionsExtensionsOwned);
impl View for CertificateRequestExtensionsOwned {
    type V = SpecCertificateRequestExtensions;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequestExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl From<CertificateRequestExtensionsOwned> for CertificateRequestExtensionsOwnedInner {
    fn ex_from(m: CertificateRequestExtensionsOwned) -> CertificateRequestExtensionsOwnedInner {
        (m.l, m.extensions)
    }
}
impl From<CertificateRequestExtensionsOwnedInner> for CertificateRequestExtensionsOwned {
    fn ex_from(m: CertificateRequestExtensionsOwnedInner) -> CertificateRequestExtensionsOwned {
        let (l, extensions) = m;
        CertificateRequestExtensionsOwned {
            l,
            extensions,
        }
    }
}

pub struct SpecCertificateRequest {
    pub certificate_request_context: SpecOpaque0Ff,
    pub extensions: SpecCertificateRequestExtensions,
}
pub type SpecCertificateRequestInner = (SpecOpaque0Ff, SpecCertificateRequestExtensions);
impl SpecFrom<SpecCertificateRequest> for SpecCertificateRequestInner {
    open spec fn spec_from(m: SpecCertificateRequest) -> SpecCertificateRequestInner {
        (m.certificate_request_context, m.extensions)
    }
}
impl SpecFrom<SpecCertificateRequestInner> for SpecCertificateRequest {
    open spec fn spec_from(m: SpecCertificateRequestInner) -> SpecCertificateRequest {
        let (certificate_request_context, extensions) = m;
        SpecCertificateRequest {
            certificate_request_context,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateRequest<'a> {
    pub certificate_request_context: Opaque0Ff<'a>,
    pub extensions: CertificateRequestExtensions<'a>,
}
pub type CertificateRequestInner<'a> = (Opaque0Ff<'a>, CertificateRequestExtensions<'a>);
impl View for CertificateRequest<'_> {
    type V = SpecCertificateRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequest {
            certificate_request_context: self.certificate_request_context@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<CertificateRequest<'a>> for CertificateRequestInner<'a> {
    fn ex_from(m: CertificateRequest<'a>) -> CertificateRequestInner<'a> {
        (m.certificate_request_context, m.extensions)
    }
}
impl<'a> From<CertificateRequestInner<'a>> for CertificateRequest<'a> {
    fn ex_from(m: CertificateRequestInner<'a>) -> CertificateRequest<'a> {
        let (certificate_request_context, extensions) = m;
        CertificateRequest {
            certificate_request_context,
            extensions,
        }
    }
}
pub struct CertificateRequestMapper;
impl View for CertificateRequestMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateRequestMapper {
    type Src = SpecCertificateRequestInner;
    type Dst = SpecCertificateRequest;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateRequestMapper {
    type Src<'a> = CertificateRequestInner<'a>;
    type Dst<'a> = CertificateRequest<'a>;
    type SrcOwned = CertificateRequestOwnedInner;
    type DstOwned = CertificateRequestOwned;
}
pub struct CertificateRequestOwned {
    pub certificate_request_context: Opaque0FfOwned,
    pub extensions: CertificateRequestExtensionsOwned,
}
pub type CertificateRequestOwnedInner = (Opaque0FfOwned, CertificateRequestExtensionsOwned);
impl View for CertificateRequestOwned {
    type V = SpecCertificateRequest;
    open spec fn view(&self) -> Self::V {
        SpecCertificateRequest {
            certificate_request_context: self.certificate_request_context@,
            extensions: self.extensions@,
        }
    }
}
impl From<CertificateRequestOwned> for CertificateRequestOwnedInner {
    fn ex_from(m: CertificateRequestOwned) -> CertificateRequestOwnedInner {
        (m.certificate_request_context, m.extensions)
    }
}
impl From<CertificateRequestOwnedInner> for CertificateRequestOwned {
    fn ex_from(m: CertificateRequestOwnedInner) -> CertificateRequestOwned {
        let (certificate_request_context, extensions) = m;
        CertificateRequestOwned {
            certificate_request_context,
            extensions,
        }
    }
}

pub struct SpecNewSessionTicketExtensions {
    pub l: SpecUint0Fffe,
    pub extensions: SpecNewSessionTicketExtensionsExtensions,
}
pub type SpecNewSessionTicketExtensionsInner = (SpecUint0Fffe, SpecNewSessionTicketExtensionsExtensions);
impl SpecFrom<SpecNewSessionTicketExtensions> for SpecNewSessionTicketExtensionsInner {
    open spec fn spec_from(m: SpecNewSessionTicketExtensions) -> SpecNewSessionTicketExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecNewSessionTicketExtensionsInner> for SpecNewSessionTicketExtensions {
    open spec fn spec_from(m: SpecNewSessionTicketExtensionsInner) -> SpecNewSessionTicketExtensions {
        let (l, extensions) = m;
        SpecNewSessionTicketExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewSessionTicketExtensions<'a> {
    pub l: Uint0Fffe,
    pub extensions: NewSessionTicketExtensionsExtensions<'a>,
}
pub type NewSessionTicketExtensionsInner<'a> = (Uint0Fffe, NewSessionTicketExtensionsExtensions<'a>);
impl View for NewSessionTicketExtensions<'_> {
    type V = SpecNewSessionTicketExtensions;
    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<NewSessionTicketExtensions<'a>> for NewSessionTicketExtensionsInner<'a> {
    fn ex_from(m: NewSessionTicketExtensions<'a>) -> NewSessionTicketExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<NewSessionTicketExtensionsInner<'a>> for NewSessionTicketExtensions<'a> {
    fn ex_from(m: NewSessionTicketExtensionsInner<'a>) -> NewSessionTicketExtensions<'a> {
        let (l, extensions) = m;
        NewSessionTicketExtensions {
            l,
            extensions,
        }
    }
}
pub struct NewSessionTicketExtensionsMapper;
impl View for NewSessionTicketExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketExtensionsMapper {
    type Src = SpecNewSessionTicketExtensionsInner;
    type Dst = SpecNewSessionTicketExtensions;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for NewSessionTicketExtensionsMapper {
    type Src<'a> = NewSessionTicketExtensionsInner<'a>;
    type Dst<'a> = NewSessionTicketExtensions<'a>;
    type SrcOwned = NewSessionTicketExtensionsOwnedInner;
    type DstOwned = NewSessionTicketExtensionsOwned;
}
pub struct NewSessionTicketExtensionsOwned {
    pub l: Uint0FffeOwned,
    pub extensions: NewSessionTicketExtensionsExtensionsOwned,
}
pub type NewSessionTicketExtensionsOwnedInner = (Uint0FffeOwned, NewSessionTicketExtensionsExtensionsOwned);
impl View for NewSessionTicketExtensionsOwned {
    type V = SpecNewSessionTicketExtensions;
    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicketExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl From<NewSessionTicketExtensionsOwned> for NewSessionTicketExtensionsOwnedInner {
    fn ex_from(m: NewSessionTicketExtensionsOwned) -> NewSessionTicketExtensionsOwnedInner {
        (m.l, m.extensions)
    }
}
impl From<NewSessionTicketExtensionsOwnedInner> for NewSessionTicketExtensionsOwned {
    fn ex_from(m: NewSessionTicketExtensionsOwnedInner) -> NewSessionTicketExtensionsOwned {
        let (l, extensions) = m;
        NewSessionTicketExtensionsOwned {
            l,
            extensions,
        }
    }
}

pub struct SpecNewSessionTicket {
    pub ticket_lifetime: u32,
    pub ticket_age_add: u32,
    pub ticket_nonce: SpecOpaque0Ff,
    pub ticket: SpecOpaque1Ffff,
    pub extensions: SpecNewSessionTicketExtensions,
}
pub type SpecNewSessionTicketInner = (u32, (u32, (SpecOpaque0Ff, (SpecOpaque1Ffff, SpecNewSessionTicketExtensions))));
impl SpecFrom<SpecNewSessionTicket> for SpecNewSessionTicketInner {
    open spec fn spec_from(m: SpecNewSessionTicket) -> SpecNewSessionTicketInner {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl SpecFrom<SpecNewSessionTicketInner> for SpecNewSessionTicket {
    open spec fn spec_from(m: SpecNewSessionTicketInner) -> SpecNewSessionTicket {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        SpecNewSessionTicket {
            ticket_lifetime,
            ticket_age_add,
            ticket_nonce,
            ticket,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NewSessionTicket<'a> {
    pub ticket_lifetime: u32,
    pub ticket_age_add: u32,
    pub ticket_nonce: Opaque0Ff<'a>,
    pub ticket: Opaque1Ffff<'a>,
    pub extensions: NewSessionTicketExtensions<'a>,
}
pub type NewSessionTicketInner<'a> = (u32, (u32, (Opaque0Ff<'a>, (Opaque1Ffff<'a>, NewSessionTicketExtensions<'a>))));
impl View for NewSessionTicket<'_> {
    type V = SpecNewSessionTicket;
    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicket {
            ticket_lifetime: self.ticket_lifetime@,
            ticket_age_add: self.ticket_age_add@,
            ticket_nonce: self.ticket_nonce@,
            ticket: self.ticket@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<NewSessionTicket<'a>> for NewSessionTicketInner<'a> {
    fn ex_from(m: NewSessionTicket<'a>) -> NewSessionTicketInner<'a> {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl<'a> From<NewSessionTicketInner<'a>> for NewSessionTicket<'a> {
    fn ex_from(m: NewSessionTicketInner<'a>) -> NewSessionTicket<'a> {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        NewSessionTicket {
            ticket_lifetime,
            ticket_age_add,
            ticket_nonce,
            ticket,
            extensions,
        }
    }
}
pub struct NewSessionTicketMapper;
impl View for NewSessionTicketMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for NewSessionTicketMapper {
    type Src = SpecNewSessionTicketInner;
    type Dst = SpecNewSessionTicket;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for NewSessionTicketMapper {
    type Src<'a> = NewSessionTicketInner<'a>;
    type Dst<'a> = NewSessionTicket<'a>;
    type SrcOwned = NewSessionTicketOwnedInner;
    type DstOwned = NewSessionTicketOwned;
}
pub struct NewSessionTicketOwned {
    pub ticket_lifetime: u32,
    pub ticket_age_add: u32,
    pub ticket_nonce: Opaque0FfOwned,
    pub ticket: Opaque1FfffOwned,
    pub extensions: NewSessionTicketExtensionsOwned,
}
pub type NewSessionTicketOwnedInner = (u32, (u32, (Opaque0FfOwned, (Opaque1FfffOwned, NewSessionTicketExtensionsOwned))));
impl View for NewSessionTicketOwned {
    type V = SpecNewSessionTicket;
    open spec fn view(&self) -> Self::V {
        SpecNewSessionTicket {
            ticket_lifetime: self.ticket_lifetime@,
            ticket_age_add: self.ticket_age_add@,
            ticket_nonce: self.ticket_nonce@,
            ticket: self.ticket@,
            extensions: self.extensions@,
        }
    }
}
impl From<NewSessionTicketOwned> for NewSessionTicketOwnedInner {
    fn ex_from(m: NewSessionTicketOwned) -> NewSessionTicketOwnedInner {
        (m.ticket_lifetime, (m.ticket_age_add, (m.ticket_nonce, (m.ticket, m.extensions))))
    }
}
impl From<NewSessionTicketOwnedInner> for NewSessionTicketOwned {
    fn ex_from(m: NewSessionTicketOwnedInner) -> NewSessionTicketOwned {
        let (ticket_lifetime, (ticket_age_add, (ticket_nonce, (ticket, extensions)))) = m;
        NewSessionTicketOwned {
            ticket_lifetime,
            ticket_age_add,
            ticket_nonce,
            ticket,
            extensions,
        }
    }
}

pub struct SpecCertificateVerify {
    pub signature_scheme: SpecSignatureScheme,
    pub signature: SpecOpaque0Ffff,
}
pub type SpecCertificateVerifyInner = (SpecSignatureScheme, SpecOpaque0Ffff);
impl SpecFrom<SpecCertificateVerify> for SpecCertificateVerifyInner {
    open spec fn spec_from(m: SpecCertificateVerify) -> SpecCertificateVerifyInner {
        (m.signature_scheme, m.signature)
    }
}
impl SpecFrom<SpecCertificateVerifyInner> for SpecCertificateVerify {
    open spec fn spec_from(m: SpecCertificateVerifyInner) -> SpecCertificateVerify {
        let (signature_scheme, signature) = m;
        SpecCertificateVerify {
            signature_scheme,
            signature,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateVerify<'a> {
    pub signature_scheme: SignatureScheme,
    pub signature: Opaque0Ffff<'a>,
}
pub type CertificateVerifyInner<'a> = (SignatureScheme, Opaque0Ffff<'a>);
impl View for CertificateVerify<'_> {
    type V = SpecCertificateVerify;
    open spec fn view(&self) -> Self::V {
        SpecCertificateVerify {
            signature_scheme: self.signature_scheme@,
            signature: self.signature@,
        }
    }
}
impl<'a> From<CertificateVerify<'a>> for CertificateVerifyInner<'a> {
    fn ex_from(m: CertificateVerify<'a>) -> CertificateVerifyInner<'a> {
        (m.signature_scheme, m.signature)
    }
}
impl<'a> From<CertificateVerifyInner<'a>> for CertificateVerify<'a> {
    fn ex_from(m: CertificateVerifyInner<'a>) -> CertificateVerify<'a> {
        let (signature_scheme, signature) = m;
        CertificateVerify {
            signature_scheme,
            signature,
        }
    }
}
pub struct CertificateVerifyMapper;
impl View for CertificateVerifyMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateVerifyMapper {
    type Src = SpecCertificateVerifyInner;
    type Dst = SpecCertificateVerify;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateVerifyMapper {
    type Src<'a> = CertificateVerifyInner<'a>;
    type Dst<'a> = CertificateVerify<'a>;
    type SrcOwned = CertificateVerifyOwnedInner;
    type DstOwned = CertificateVerifyOwned;
}
pub struct CertificateVerifyOwned {
    pub signature_scheme: SignatureSchemeOwned,
    pub signature: Opaque0FfffOwned,
}
pub type CertificateVerifyOwnedInner = (SignatureSchemeOwned, Opaque0FfffOwned);
impl View for CertificateVerifyOwned {
    type V = SpecCertificateVerify;
    open spec fn view(&self) -> Self::V {
        SpecCertificateVerify {
            signature_scheme: self.signature_scheme@,
            signature: self.signature@,
        }
    }
}
impl From<CertificateVerifyOwned> for CertificateVerifyOwnedInner {
    fn ex_from(m: CertificateVerifyOwned) -> CertificateVerifyOwnedInner {
        (m.signature_scheme, m.signature)
    }
}
impl From<CertificateVerifyOwnedInner> for CertificateVerifyOwned {
    fn ex_from(m: CertificateVerifyOwnedInner) -> CertificateVerifyOwned {
        let (signature_scheme, signature) = m;
        CertificateVerifyOwned {
            signature_scheme,
            signature,
        }
    }
}


#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum ContentType {
    Invalid = 0,
ChangeCipherSpec = 20,
Alert = 21,
Handshake = 22,
ApplicationData = 23
}
pub type SpecContentType = ContentType;
pub type ContentTypeOwned = ContentType;

pub type ContentTypeInner = u8;

impl View for ContentType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<ContentTypeInner> for ContentType {
    type Error = ();

    open spec fn spec_try_from(v: ContentTypeInner) -> Result<ContentType, ()> {
        match v {
            0u8 => Ok(ContentType::Invalid),
            20u8 => Ok(ContentType::ChangeCipherSpec),
            21u8 => Ok(ContentType::Alert),
            22u8 => Ok(ContentType::Handshake),
            23u8 => Ok(ContentType::ApplicationData),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<ContentType> for ContentTypeInner {
    type Error = ();

    open spec fn spec_try_from(v: ContentType) -> Result<ContentTypeInner, ()> {
        match v {
            ContentType::Invalid => Ok(0u8),
            ContentType::ChangeCipherSpec => Ok(20u8),
            ContentType::Alert => Ok(21u8),
            ContentType::Handshake => Ok(22u8),
            ContentType::ApplicationData => Ok(23u8),
        }
    }
}

impl TryFrom<ContentTypeInner> for ContentType {
    type Error = ();

    fn ex_try_from(v: ContentTypeInner) -> Result<ContentType, ()> {
        match v {
            0u8 => Ok(ContentType::Invalid),
            20u8 => Ok(ContentType::ChangeCipherSpec),
            21u8 => Ok(ContentType::Alert),
            22u8 => Ok(ContentType::Handshake),
            23u8 => Ok(ContentType::ApplicationData),
            _ => Err(()),
        }
    }
}

impl TryFrom<ContentType> for ContentTypeInner {
    type Error = ();

    fn ex_try_from(v: ContentType) -> Result<ContentTypeInner, ()> {
        match v {
            ContentType::Invalid => Ok(0u8),
            ContentType::ChangeCipherSpec => Ok(20u8),
            ContentType::Alert => Ok(21u8),
            ContentType::Handshake => Ok(22u8),
            ContentType::ApplicationData => Ok(23u8),
        }
    }
}

pub struct ContentTypeMapper;

impl View for ContentTypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for ContentTypeMapper {
    type Src = ContentTypeInner;
    type Dst = ContentType;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for ContentTypeMapper {
    type Src<'a> = ContentTypeInner;
    type Dst<'a> = ContentType;

    type SrcOwned = ContentTypeInner;
    type DstOwned = ContentType;
}

pub struct SpecTlsPlaintext {
    pub content_type: SpecContentType,
    pub legacy_record_version: SpecProtocolVersion,
    pub fragment: SpecOpaque0Ffff,
}
pub type SpecTlsPlaintextInner = (SpecContentType, (SpecProtocolVersion, SpecOpaque0Ffff));
impl SpecFrom<SpecTlsPlaintext> for SpecTlsPlaintextInner {
    open spec fn spec_from(m: SpecTlsPlaintext) -> SpecTlsPlaintextInner {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl SpecFrom<SpecTlsPlaintextInner> for SpecTlsPlaintext {
    open spec fn spec_from(m: SpecTlsPlaintextInner) -> SpecTlsPlaintext {
        let (content_type, (legacy_record_version, fragment)) = m;
        SpecTlsPlaintext {
            content_type,
            legacy_record_version,
            fragment,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsPlaintext<'a> {
    pub content_type: ContentType,
    pub legacy_record_version: ProtocolVersion,
    pub fragment: Opaque0Ffff<'a>,
}
pub type TlsPlaintextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
impl View for TlsPlaintext<'_> {
    type V = SpecTlsPlaintext;
    open spec fn view(&self) -> Self::V {
        SpecTlsPlaintext {
            content_type: self.content_type@,
            legacy_record_version: self.legacy_record_version@,
            fragment: self.fragment@,
        }
    }
}
impl<'a> From<TlsPlaintext<'a>> for TlsPlaintextInner<'a> {
    fn ex_from(m: TlsPlaintext<'a>) -> TlsPlaintextInner<'a> {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl<'a> From<TlsPlaintextInner<'a>> for TlsPlaintext<'a> {
    fn ex_from(m: TlsPlaintextInner<'a>) -> TlsPlaintext<'a> {
        let (content_type, (legacy_record_version, fragment)) = m;
        TlsPlaintext {
            content_type,
            legacy_record_version,
            fragment,
        }
    }
}
pub struct TlsPlaintextMapper;
impl View for TlsPlaintextMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsPlaintextMapper {
    type Src = SpecTlsPlaintextInner;
    type Dst = SpecTlsPlaintext;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for TlsPlaintextMapper {
    type Src<'a> = TlsPlaintextInner<'a>;
    type Dst<'a> = TlsPlaintext<'a>;
    type SrcOwned = TlsPlaintextOwnedInner;
    type DstOwned = TlsPlaintextOwned;
}
pub struct TlsPlaintextOwned {
    pub content_type: ContentTypeOwned,
    pub legacy_record_version: ProtocolVersionOwned,
    pub fragment: Opaque0FfffOwned,
}
pub type TlsPlaintextOwnedInner = (ContentTypeOwned, (ProtocolVersionOwned, Opaque0FfffOwned));
impl View for TlsPlaintextOwned {
    type V = SpecTlsPlaintext;
    open spec fn view(&self) -> Self::V {
        SpecTlsPlaintext {
            content_type: self.content_type@,
            legacy_record_version: self.legacy_record_version@,
            fragment: self.fragment@,
        }
    }
}
impl From<TlsPlaintextOwned> for TlsPlaintextOwnedInner {
    fn ex_from(m: TlsPlaintextOwned) -> TlsPlaintextOwnedInner {
        (m.content_type, (m.legacy_record_version, m.fragment))
    }
}
impl From<TlsPlaintextOwnedInner> for TlsPlaintextOwned {
    fn ex_from(m: TlsPlaintextOwnedInner) -> TlsPlaintextOwned {
        let (content_type, (legacy_record_version, fragment)) = m;
        TlsPlaintextOwned {
            content_type,
            legacy_record_version,
            fragment,
        }
    }
}

pub enum SpecSeverHelloExtensionExtensionData {
    ServerName(SpecServerNameList),
    MaxFragmentLength(SpecMaxFragmentLength),
    StatusRequest(SpecCertificateStatusRequest),
    SupportedGroups(SpecNamedGroupList),
    ECPointFormats(SpecEcPointFormatList),
    SignatureAlgorithms(SpecSignatureSchemeList),
    UseSRTP(SpecSrtpProtectionProfiles),
    Heartbeat(SpecHeartbeatMode),
    ApplicationLayerProtocolNegotiation(SpecProtocolNameList),
    SigedCertificateTimestamp(SpecSignedCertificateTimestampList),
    ClientCertificateType(SpecClientCertTypeClientExtension),
    ServerCertificateType(SpecServerCertTypeClientExtension),
    Padding(SpecPaddingExtension),
    EncryptThenMac(SpecEmpty),
    ExtendedMasterSecret(SpecEmpty),
    SessionTicket(SpecEmpty),
    PreSharedKey(SpecPreSharedKeyClientExtension),
    EarlyData(SpecEmpty),
    SupportedVersions(SpecSupportedVersionsClient),
    Cookie(SpecCookie),
    PskKeyExchangeModes(SpecPskKeyExchangeModes),
    CertificateAuthorities(SpecCertificateAuthoritiesExtension),
    OidFilters(SpecOidFilterExtension),
    PostHandshakeAuth(SpecEmpty),
    SignatureAlgorithmsCert(SpecSignatureSchemeList),
    KeyShare(SpecKeyShareClientHello),
    Unrecognized(Seq<u8>),
}
pub type SpecSeverHelloExtensionExtensionDataInner = Either<SpecServerNameList, Either<SpecMaxFragmentLength, Either<SpecCertificateStatusRequest, Either<SpecNamedGroupList, Either<SpecEcPointFormatList, Either<SpecSignatureSchemeList, Either<SpecSrtpProtectionProfiles, Either<SpecHeartbeatMode, Either<SpecProtocolNameList, Either<SpecSignedCertificateTimestampList, Either<SpecClientCertTypeClientExtension, Either<SpecServerCertTypeClientExtension, Either<SpecPaddingExtension, Either<SpecEmpty, Either<SpecEmpty, Either<SpecEmpty, Either<SpecPreSharedKeyClientExtension, Either<SpecEmpty, Either<SpecSupportedVersionsClient, Either<SpecCookie, Either<SpecPskKeyExchangeModes, Either<SpecCertificateAuthoritiesExtension, Either<SpecOidFilterExtension, Either<SpecEmpty, Either<SpecSignatureSchemeList, Either<SpecKeyShareClientHello, Seq<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl SpecFrom<SpecSeverHelloExtensionExtensionData> for SpecSeverHelloExtensionExtensionDataInner {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionData) -> SpecSeverHelloExtensionExtensionDataInner {
        match m {
            SpecSeverHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SpecSeverHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecSeverHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecSeverHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecSeverHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecSeverHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SpecSeverHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SpecSeverHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SpecSeverHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SpecSeverHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SpecSeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl SpecFrom<SpecSeverHelloExtensionExtensionDataInner> for SpecSeverHelloExtensionExtensionData {
    open spec fn spec_from(m: SpecSeverHelloExtensionExtensionDataInner) -> SpecSeverHelloExtensionExtensionData {
        match m {
            Either::Left(m) => SpecSeverHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecSeverHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecSeverHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecSeverHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecSeverHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecSeverHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SpecSeverHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SpecSeverHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SpecSeverHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SpecSeverHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SpecSeverHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SpecSeverHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SpecSeverHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeverHelloExtensionExtensionData<'a> {
    ServerName(ServerNameList<'a>),
    MaxFragmentLength(MaxFragmentLength),
    StatusRequest(CertificateStatusRequest<'a>),
    SupportedGroups(NamedGroupList),
    ECPointFormats(EcPointFormatList),
    SignatureAlgorithms(SignatureSchemeList),
    UseSRTP(SrtpProtectionProfiles<'a>),
    Heartbeat(HeartbeatMode),
    ApplicationLayerProtocolNegotiation(ProtocolNameList<'a>),
    SigedCertificateTimestamp(SignedCertificateTimestampList<'a>),
    ClientCertificateType(ClientCertTypeClientExtension),
    ServerCertificateType(ServerCertTypeClientExtension),
    Padding(PaddingExtension),
    EncryptThenMac(Empty<'a>),
    ExtendedMasterSecret(Empty<'a>),
    SessionTicket(Empty<'a>),
    PreSharedKey(PreSharedKeyClientExtension<'a>),
    EarlyData(Empty<'a>),
    SupportedVersions(SupportedVersionsClient),
    Cookie(Cookie<'a>),
    PskKeyExchangeModes(PskKeyExchangeModes),
    CertificateAuthorities(CertificateAuthoritiesExtension<'a>),
    OidFilters(OidFilterExtension<'a>),
    PostHandshakeAuth(Empty<'a>),
    SignatureAlgorithmsCert(SignatureSchemeList),
    KeyShare(KeyShareClientHello<'a>),
    Unrecognized(&'a [u8]),
}
pub type SeverHelloExtensionExtensionDataInner<'a> = Either<ServerNameList<'a>, Either<MaxFragmentLength, Either<CertificateStatusRequest<'a>, Either<NamedGroupList, Either<EcPointFormatList, Either<SignatureSchemeList, Either<SrtpProtectionProfiles<'a>, Either<HeartbeatMode, Either<ProtocolNameList<'a>, Either<SignedCertificateTimestampList<'a>, Either<ClientCertTypeClientExtension, Either<ServerCertTypeClientExtension, Either<PaddingExtension, Either<Empty<'a>, Either<Empty<'a>, Either<Empty<'a>, Either<PreSharedKeyClientExtension<'a>, Either<Empty<'a>, Either<SupportedVersionsClient, Either<Cookie<'a>, Either<PskKeyExchangeModes, Either<CertificateAuthoritiesExtension<'a>, Either<OidFilterExtension<'a>, Either<Empty<'a>, Either<SignatureSchemeList, Either<KeyShareClientHello<'a>, &'a [u8]>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for SeverHelloExtensionExtensionData<'_> {
    type V = SpecSeverHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            SeverHelloExtensionExtensionData::ServerName(m) => SpecSeverHelloExtensionExtensionData::ServerName(m@),
            SeverHelloExtensionExtensionData::MaxFragmentLength(m) => SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m@),
            SeverHelloExtensionExtensionData::StatusRequest(m) => SpecSeverHelloExtensionExtensionData::StatusRequest(m@),
            SeverHelloExtensionExtensionData::SupportedGroups(m) => SpecSeverHelloExtensionExtensionData::SupportedGroups(m@),
            SeverHelloExtensionExtensionData::ECPointFormats(m) => SpecSeverHelloExtensionExtensionData::ECPointFormats(m@),
            SeverHelloExtensionExtensionData::SignatureAlgorithms(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m@),
            SeverHelloExtensionExtensionData::UseSRTP(m) => SpecSeverHelloExtensionExtensionData::UseSRTP(m@),
            SeverHelloExtensionExtensionData::Heartbeat(m) => SpecSeverHelloExtensionExtensionData::Heartbeat(m@),
            SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            SeverHelloExtensionExtensionData::ClientCertificateType(m) => SpecSeverHelloExtensionExtensionData::ClientCertificateType(m@),
            SeverHelloExtensionExtensionData::ServerCertificateType(m) => SpecSeverHelloExtensionExtensionData::ServerCertificateType(m@),
            SeverHelloExtensionExtensionData::Padding(m) => SpecSeverHelloExtensionExtensionData::Padding(m@),
            SeverHelloExtensionExtensionData::EncryptThenMac(m) => SpecSeverHelloExtensionExtensionData::EncryptThenMac(m@),
            SeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            SeverHelloExtensionExtensionData::SessionTicket(m) => SpecSeverHelloExtensionExtensionData::SessionTicket(m@),
            SeverHelloExtensionExtensionData::PreSharedKey(m) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m@),
            SeverHelloExtensionExtensionData::EarlyData(m) => SpecSeverHelloExtensionExtensionData::EarlyData(m@),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m@),
            SeverHelloExtensionExtensionData::Cookie(m) => SpecSeverHelloExtensionExtensionData::Cookie(m@),
            SeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            SeverHelloExtensionExtensionData::CertificateAuthorities(m) => SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m@),
            SeverHelloExtensionExtensionData::OidFilters(m) => SpecSeverHelloExtensionExtensionData::OidFilters(m@),
            SeverHelloExtensionExtensionData::PostHandshakeAuth(m) => SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m@),
            SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            SeverHelloExtensionExtensionData::KeyShare(m) => SpecSeverHelloExtensionExtensionData::KeyShare(m@),
            SeverHelloExtensionExtensionData::Unrecognized(m) => SpecSeverHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}
impl<'a> From<SeverHelloExtensionExtensionData<'a>> for SeverHelloExtensionExtensionDataInner<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionData<'a>) -> SeverHelloExtensionExtensionDataInner<'a> {
        match m {
            SeverHelloExtensionExtensionData::ServerName(m) => Either::Left(m),
            SeverHelloExtensionExtensionData::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SeverHelloExtensionExtensionData::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SeverHelloExtensionExtensionData::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SeverHelloExtensionExtensionData::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SeverHelloExtensionExtensionData::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SeverHelloExtensionExtensionData::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SeverHelloExtensionExtensionData::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SeverHelloExtensionExtensionData::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SeverHelloExtensionExtensionData::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SeverHelloExtensionExtensionData::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SeverHelloExtensionExtensionData::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SeverHelloExtensionExtensionData::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SeverHelloExtensionExtensionData::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SeverHelloExtensionExtensionData::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SeverHelloExtensionExtensionData::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SeverHelloExtensionExtensionData::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SeverHelloExtensionExtensionData::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SeverHelloExtensionExtensionData::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SeverHelloExtensionExtensionData::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SeverHelloExtensionExtensionData::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SeverHelloExtensionExtensionData::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl<'a> From<SeverHelloExtensionExtensionDataInner<'a>> for SeverHelloExtensionExtensionData<'a> {
    fn ex_from(m: SeverHelloExtensionExtensionDataInner<'a>) -> SeverHelloExtensionExtensionData<'a> {
        match m {
            Either::Left(m) => SeverHelloExtensionExtensionData::ServerName(m),
            Either::Right(Either::Left(m)) => SeverHelloExtensionExtensionData::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SeverHelloExtensionExtensionData::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SeverHelloExtensionExtensionData::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SeverHelloExtensionExtensionData::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SeverHelloExtensionExtensionData::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SeverHelloExtensionExtensionData::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SeverHelloExtensionExtensionData::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SeverHelloExtensionExtensionData::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SeverHelloExtensionExtensionData::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SeverHelloExtensionExtensionData::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SeverHelloExtensionExtensionData::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SeverHelloExtensionExtensionData::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SeverHelloExtensionExtensionData::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SeverHelloExtensionExtensionData::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SeverHelloExtensionExtensionData::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SeverHelloExtensionExtensionData::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SeverHelloExtensionExtensionData::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SeverHelloExtensionExtensionData::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SeverHelloExtensionExtensionData::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SeverHelloExtensionExtensionData::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SeverHelloExtensionExtensionData::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SeverHelloExtensionExtensionData::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionData::Unrecognized(m),
        }
    }
}
pub struct SeverHelloExtensionExtensionDataMapper;
impl View for SeverHelloExtensionExtensionDataMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionExtensionDataMapper {
    type Src = SpecSeverHelloExtensionExtensionDataInner;
    type Dst = SpecSeverHelloExtensionExtensionData;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SeverHelloExtensionExtensionDataMapper {
    type Src<'a> = SeverHelloExtensionExtensionDataInner<'a>;
    type Dst<'a> = SeverHelloExtensionExtensionData<'a>;
    type SrcOwned = SeverHelloExtensionExtensionDataOwnedInner;
    type DstOwned = SeverHelloExtensionExtensionDataOwned;
}
pub enum SeverHelloExtensionExtensionDataOwned {
    ServerName(ServerNameListOwned),
    MaxFragmentLength(MaxFragmentLengthOwned),
    StatusRequest(CertificateStatusRequestOwned),
    SupportedGroups(NamedGroupListOwned),
    ECPointFormats(EcPointFormatListOwned),
    SignatureAlgorithms(SignatureSchemeListOwned),
    UseSRTP(SrtpProtectionProfilesOwned),
    Heartbeat(HeartbeatModeOwned),
    ApplicationLayerProtocolNegotiation(ProtocolNameListOwned),
    SigedCertificateTimestamp(SignedCertificateTimestampListOwned),
    ClientCertificateType(ClientCertTypeClientExtensionOwned),
    ServerCertificateType(ServerCertTypeClientExtensionOwned),
    Padding(PaddingExtensionOwned),
    EncryptThenMac(EmptyOwned),
    ExtendedMasterSecret(EmptyOwned),
    SessionTicket(EmptyOwned),
    PreSharedKey(PreSharedKeyClientExtensionOwned),
    EarlyData(EmptyOwned),
    SupportedVersions(SupportedVersionsClientOwned),
    Cookie(CookieOwned),
    PskKeyExchangeModes(PskKeyExchangeModesOwned),
    CertificateAuthorities(CertificateAuthoritiesExtensionOwned),
    OidFilters(OidFilterExtensionOwned),
    PostHandshakeAuth(EmptyOwned),
    SignatureAlgorithmsCert(SignatureSchemeListOwned),
    KeyShare(KeyShareClientHelloOwned),
    Unrecognized(Vec<u8>),
}
pub type SeverHelloExtensionExtensionDataOwnedInner = Either<ServerNameListOwned, Either<MaxFragmentLengthOwned, Either<CertificateStatusRequestOwned, Either<NamedGroupListOwned, Either<EcPointFormatListOwned, Either<SignatureSchemeListOwned, Either<SrtpProtectionProfilesOwned, Either<HeartbeatModeOwned, Either<ProtocolNameListOwned, Either<SignedCertificateTimestampListOwned, Either<ClientCertTypeClientExtensionOwned, Either<ServerCertTypeClientExtensionOwned, Either<PaddingExtensionOwned, Either<EmptyOwned, Either<EmptyOwned, Either<EmptyOwned, Either<PreSharedKeyClientExtensionOwned, Either<EmptyOwned, Either<SupportedVersionsClientOwned, Either<CookieOwned, Either<PskKeyExchangeModesOwned, Either<CertificateAuthoritiesExtensionOwned, Either<OidFilterExtensionOwned, Either<EmptyOwned, Either<SignatureSchemeListOwned, Either<KeyShareClientHelloOwned, Vec<u8>>>>>>>>>>>>>>>>>>>>>>>>>>>;
impl View for SeverHelloExtensionExtensionDataOwned {
    type V = SpecSeverHelloExtensionExtensionData;
    open spec fn view(&self) -> Self::V {
        match self {
            SeverHelloExtensionExtensionDataOwned::ServerName(m) => SpecSeverHelloExtensionExtensionData::ServerName(m@),
            SeverHelloExtensionExtensionDataOwned::MaxFragmentLength(m) => SpecSeverHelloExtensionExtensionData::MaxFragmentLength(m@),
            SeverHelloExtensionExtensionDataOwned::StatusRequest(m) => SpecSeverHelloExtensionExtensionData::StatusRequest(m@),
            SeverHelloExtensionExtensionDataOwned::SupportedGroups(m) => SpecSeverHelloExtensionExtensionData::SupportedGroups(m@),
            SeverHelloExtensionExtensionDataOwned::ECPointFormats(m) => SpecSeverHelloExtensionExtensionData::ECPointFormats(m@),
            SeverHelloExtensionExtensionDataOwned::SignatureAlgorithms(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithms(m@),
            SeverHelloExtensionExtensionDataOwned::UseSRTP(m) => SpecSeverHelloExtensionExtensionData::UseSRTP(m@),
            SeverHelloExtensionExtensionDataOwned::Heartbeat(m) => SpecSeverHelloExtensionExtensionData::Heartbeat(m@),
            SeverHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m) => SpecSeverHelloExtensionExtensionData::ApplicationLayerProtocolNegotiation(m@),
            SeverHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m) => SpecSeverHelloExtensionExtensionData::SigedCertificateTimestamp(m@),
            SeverHelloExtensionExtensionDataOwned::ClientCertificateType(m) => SpecSeverHelloExtensionExtensionData::ClientCertificateType(m@),
            SeverHelloExtensionExtensionDataOwned::ServerCertificateType(m) => SpecSeverHelloExtensionExtensionData::ServerCertificateType(m@),
            SeverHelloExtensionExtensionDataOwned::Padding(m) => SpecSeverHelloExtensionExtensionData::Padding(m@),
            SeverHelloExtensionExtensionDataOwned::EncryptThenMac(m) => SpecSeverHelloExtensionExtensionData::EncryptThenMac(m@),
            SeverHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m) => SpecSeverHelloExtensionExtensionData::ExtendedMasterSecret(m@),
            SeverHelloExtensionExtensionDataOwned::SessionTicket(m) => SpecSeverHelloExtensionExtensionData::SessionTicket(m@),
            SeverHelloExtensionExtensionDataOwned::PreSharedKey(m) => SpecSeverHelloExtensionExtensionData::PreSharedKey(m@),
            SeverHelloExtensionExtensionDataOwned::EarlyData(m) => SpecSeverHelloExtensionExtensionData::EarlyData(m@),
            SeverHelloExtensionExtensionDataOwned::SupportedVersions(m) => SpecSeverHelloExtensionExtensionData::SupportedVersions(m@),
            SeverHelloExtensionExtensionDataOwned::Cookie(m) => SpecSeverHelloExtensionExtensionData::Cookie(m@),
            SeverHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m) => SpecSeverHelloExtensionExtensionData::PskKeyExchangeModes(m@),
            SeverHelloExtensionExtensionDataOwned::CertificateAuthorities(m) => SpecSeverHelloExtensionExtensionData::CertificateAuthorities(m@),
            SeverHelloExtensionExtensionDataOwned::OidFilters(m) => SpecSeverHelloExtensionExtensionData::OidFilters(m@),
            SeverHelloExtensionExtensionDataOwned::PostHandshakeAuth(m) => SpecSeverHelloExtensionExtensionData::PostHandshakeAuth(m@),
            SeverHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m) => SpecSeverHelloExtensionExtensionData::SignatureAlgorithmsCert(m@),
            SeverHelloExtensionExtensionDataOwned::KeyShare(m) => SpecSeverHelloExtensionExtensionData::KeyShare(m@),
            SeverHelloExtensionExtensionDataOwned::Unrecognized(m) => SpecSeverHelloExtensionExtensionData::Unrecognized(m@),
        }
    }
}
impl From<SeverHelloExtensionExtensionDataOwned> for SeverHelloExtensionExtensionDataOwnedInner {
    fn ex_from(m: SeverHelloExtensionExtensionDataOwned) -> SeverHelloExtensionExtensionDataOwnedInner {
        match m {
            SeverHelloExtensionExtensionDataOwned::ServerName(m) => Either::Left(m),
            SeverHelloExtensionExtensionDataOwned::MaxFragmentLength(m) => Either::Right(Either::Left(m)),
            SeverHelloExtensionExtensionDataOwned::StatusRequest(m) => Either::Right(Either::Right(Either::Left(m))),
            SeverHelloExtensionExtensionDataOwned::SupportedGroups(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SeverHelloExtensionExtensionDataOwned::ECPointFormats(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SeverHelloExtensionExtensionDataOwned::SignatureAlgorithms(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SeverHelloExtensionExtensionDataOwned::UseSRTP(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SeverHelloExtensionExtensionDataOwned::Heartbeat(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SeverHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SeverHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))),
            SeverHelloExtensionExtensionDataOwned::ClientCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))),
            SeverHelloExtensionExtensionDataOwned::ServerCertificateType(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))),
            SeverHelloExtensionExtensionDataOwned::Padding(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))),
            SeverHelloExtensionExtensionDataOwned::EncryptThenMac(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))),
            SeverHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::SessionTicket(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::PreSharedKey(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::EarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::SupportedVersions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::Cookie(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::CertificateAuthorities(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::OidFilters(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::PostHandshakeAuth(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::KeyShare(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))),
            SeverHelloExtensionExtensionDataOwned::Unrecognized(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))),
        }
    }
}
impl From<SeverHelloExtensionExtensionDataOwnedInner> for SeverHelloExtensionExtensionDataOwned {
    fn ex_from(m: SeverHelloExtensionExtensionDataOwnedInner) -> SeverHelloExtensionExtensionDataOwned {
        match m {
            Either::Left(m) => SeverHelloExtensionExtensionDataOwned::ServerName(m),
            Either::Right(Either::Left(m)) => SeverHelloExtensionExtensionDataOwned::MaxFragmentLength(m),
            Either::Right(Either::Right(Either::Left(m))) => SeverHelloExtensionExtensionDataOwned::StatusRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SeverHelloExtensionExtensionDataOwned::SupportedGroups(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SeverHelloExtensionExtensionDataOwned::ECPointFormats(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SeverHelloExtensionExtensionDataOwned::SignatureAlgorithms(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SeverHelloExtensionExtensionDataOwned::UseSRTP(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SeverHelloExtensionExtensionDataOwned::Heartbeat(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SeverHelloExtensionExtensionDataOwned::ApplicationLayerProtocolNegotiation(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))) => SeverHelloExtensionExtensionDataOwned::SigedCertificateTimestamp(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))) => SeverHelloExtensionExtensionDataOwned::ClientCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))) => SeverHelloExtensionExtensionDataOwned::ServerCertificateType(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))) => SeverHelloExtensionExtensionDataOwned::Padding(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))) => SeverHelloExtensionExtensionDataOwned::EncryptThenMac(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))) => SeverHelloExtensionExtensionDataOwned::ExtendedMasterSecret(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))) => SeverHelloExtensionExtensionDataOwned::SessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::PreSharedKey(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::EarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::SupportedVersions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::Cookie(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::PskKeyExchangeModes(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::CertificateAuthorities(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::OidFilters(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::PostHandshakeAuth(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::SignatureAlgorithmsCert(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::KeyShare(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m)))))))))))))))))))))))))) => SeverHelloExtensionExtensionDataOwned::Unrecognized(m),
        }
    }
}

pub struct SpecSeverHelloExtension {
    pub extension_type: SpecExtensionType,
    pub ext_len: u16,
    pub extension_data: SpecSeverHelloExtensionExtensionData,
}
pub type SpecSeverHelloExtensionInner = ((SpecExtensionType, u16), SpecSeverHelloExtensionExtensionData);
impl SpecFrom<SpecSeverHelloExtension> for SpecSeverHelloExtensionInner {
    open spec fn spec_from(m: SpecSeverHelloExtension) -> SpecSeverHelloExtensionInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl SpecFrom<SpecSeverHelloExtensionInner> for SpecSeverHelloExtension {
    open spec fn spec_from(m: SpecSeverHelloExtensionInner) -> SpecSeverHelloExtension {
        let ((extension_type, ext_len), extension_data) = m;
        SpecSeverHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SeverHelloExtension<'a> {
    pub extension_type: ExtensionType,
    pub ext_len: u16,
    pub extension_data: SeverHelloExtensionExtensionData<'a>,
}
pub type SeverHelloExtensionInner<'a> = ((ExtensionType, u16), SeverHelloExtensionExtensionData<'a>);
impl View for SeverHelloExtension<'_> {
    type V = SpecSeverHelloExtension;
    open spec fn view(&self) -> Self::V {
        SpecSeverHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
impl<'a> From<SeverHelloExtension<'a>> for SeverHelloExtensionInner<'a> {
    fn ex_from(m: SeverHelloExtension<'a>) -> SeverHelloExtensionInner<'a> {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl<'a> From<SeverHelloExtensionInner<'a>> for SeverHelloExtension<'a> {
    fn ex_from(m: SeverHelloExtensionInner<'a>) -> SeverHelloExtension<'a> {
        let ((extension_type, ext_len), extension_data) = m;
        SeverHelloExtension {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}
pub struct SeverHelloExtensionMapper;
impl View for SeverHelloExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for SeverHelloExtensionMapper {
    type Src = SpecSeverHelloExtensionInner;
    type Dst = SpecSeverHelloExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for SeverHelloExtensionMapper {
    type Src<'a> = SeverHelloExtensionInner<'a>;
    type Dst<'a> = SeverHelloExtension<'a>;
    type SrcOwned = SeverHelloExtensionOwnedInner;
    type DstOwned = SeverHelloExtensionOwned;
}
pub struct SeverHelloExtensionOwned {
    pub extension_type: ExtensionTypeOwned,
    pub ext_len: u16,
    pub extension_data: SeverHelloExtensionExtensionDataOwned,
}
pub type SeverHelloExtensionOwnedInner = ((ExtensionTypeOwned, u16), SeverHelloExtensionExtensionDataOwned);
impl View for SeverHelloExtensionOwned {
    type V = SpecSeverHelloExtension;
    open spec fn view(&self) -> Self::V {
        SpecSeverHelloExtension {
            extension_type: self.extension_type@,
            ext_len: self.ext_len@,
            extension_data: self.extension_data@,
        }
    }
}
impl From<SeverHelloExtensionOwned> for SeverHelloExtensionOwnedInner {
    fn ex_from(m: SeverHelloExtensionOwned) -> SeverHelloExtensionOwnedInner {
        ((m.extension_type, m.ext_len), m.extension_data)
    }
}
impl From<SeverHelloExtensionOwnedInner> for SeverHelloExtensionOwned {
    fn ex_from(m: SeverHelloExtensionOwnedInner) -> SeverHelloExtensionOwned {
        let ((extension_type, ext_len), extension_data) = m;
        SeverHelloExtensionOwned {
            extension_type,
            ext_len,
            extension_data,
        }
    }
}


#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum HandshakeType {
    ClientHello = 1,
ServerHello = 2,
NewSessionTicket = 4,
EndOfEarlyData = 5,
EncryptedExtensions = 8,
Certificate = 11,
CertificateRequest = 13,
CertificateVerify = 15,
Finished = 20,
KeyUpdate = 24
}
pub type SpecHandshakeType = HandshakeType;
pub type HandshakeTypeOwned = HandshakeType;

pub type HandshakeTypeInner = u8;

impl View for HandshakeType {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<HandshakeTypeInner> for HandshakeType {
    type Error = ();

    open spec fn spec_try_from(v: HandshakeTypeInner) -> Result<HandshakeType, ()> {
        match v {
            1u8 => Ok(HandshakeType::ClientHello),
            2u8 => Ok(HandshakeType::ServerHello),
            4u8 => Ok(HandshakeType::NewSessionTicket),
            5u8 => Ok(HandshakeType::EndOfEarlyData),
            8u8 => Ok(HandshakeType::EncryptedExtensions),
            11u8 => Ok(HandshakeType::Certificate),
            13u8 => Ok(HandshakeType::CertificateRequest),
            15u8 => Ok(HandshakeType::CertificateVerify),
            20u8 => Ok(HandshakeType::Finished),
            24u8 => Ok(HandshakeType::KeyUpdate),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<HandshakeType> for HandshakeTypeInner {
    type Error = ();

    open spec fn spec_try_from(v: HandshakeType) -> Result<HandshakeTypeInner, ()> {
        match v {
            HandshakeType::ClientHello => Ok(1u8),
            HandshakeType::ServerHello => Ok(2u8),
            HandshakeType::NewSessionTicket => Ok(4u8),
            HandshakeType::EndOfEarlyData => Ok(5u8),
            HandshakeType::EncryptedExtensions => Ok(8u8),
            HandshakeType::Certificate => Ok(11u8),
            HandshakeType::CertificateRequest => Ok(13u8),
            HandshakeType::CertificateVerify => Ok(15u8),
            HandshakeType::Finished => Ok(20u8),
            HandshakeType::KeyUpdate => Ok(24u8),
        }
    }
}

impl TryFrom<HandshakeTypeInner> for HandshakeType {
    type Error = ();

    fn ex_try_from(v: HandshakeTypeInner) -> Result<HandshakeType, ()> {
        match v {
            1u8 => Ok(HandshakeType::ClientHello),
            2u8 => Ok(HandshakeType::ServerHello),
            4u8 => Ok(HandshakeType::NewSessionTicket),
            5u8 => Ok(HandshakeType::EndOfEarlyData),
            8u8 => Ok(HandshakeType::EncryptedExtensions),
            11u8 => Ok(HandshakeType::Certificate),
            13u8 => Ok(HandshakeType::CertificateRequest),
            15u8 => Ok(HandshakeType::CertificateVerify),
            20u8 => Ok(HandshakeType::Finished),
            24u8 => Ok(HandshakeType::KeyUpdate),
            _ => Err(()),
        }
    }
}

impl TryFrom<HandshakeType> for HandshakeTypeInner {
    type Error = ();

    fn ex_try_from(v: HandshakeType) -> Result<HandshakeTypeInner, ()> {
        match v {
            HandshakeType::ClientHello => Ok(1u8),
            HandshakeType::ServerHello => Ok(2u8),
            HandshakeType::NewSessionTicket => Ok(4u8),
            HandshakeType::EndOfEarlyData => Ok(5u8),
            HandshakeType::EncryptedExtensions => Ok(8u8),
            HandshakeType::Certificate => Ok(11u8),
            HandshakeType::CertificateRequest => Ok(13u8),
            HandshakeType::CertificateVerify => Ok(15u8),
            HandshakeType::Finished => Ok(20u8),
            HandshakeType::KeyUpdate => Ok(24u8),
        }
    }
}

pub struct HandshakeTypeMapper;

impl View for HandshakeTypeMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for HandshakeTypeMapper {
    type Src = HandshakeTypeInner;
    type Dst = HandshakeType;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for HandshakeTypeMapper {
    type Src<'a> = HandshakeTypeInner;
    type Dst<'a> = HandshakeType;

    type SrcOwned = HandshakeTypeInner;
    type DstOwned = HandshakeType;
}

pub type SpecServerExtensionsExtensions = Seq<SpecSeverHelloExtension>;
pub type ServerExtensionsExtensions<'a> = RepeatResult<SeverHelloExtension<'a>>;
pub type ServerExtensionsExtensionsOwned = RepeatResult<SeverHelloExtensionOwned>;

pub struct SpecServerExtensions {
    pub l: u16,
    pub extensions: SpecServerExtensionsExtensions,
}
pub type SpecServerExtensionsInner = (u16, SpecServerExtensionsExtensions);
impl SpecFrom<SpecServerExtensions> for SpecServerExtensionsInner {
    open spec fn spec_from(m: SpecServerExtensions) -> SpecServerExtensionsInner {
        (m.l, m.extensions)
    }
}
impl SpecFrom<SpecServerExtensionsInner> for SpecServerExtensions {
    open spec fn spec_from(m: SpecServerExtensionsInner) -> SpecServerExtensions {
        let (l, extensions) = m;
        SpecServerExtensions {
            l,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerExtensions<'a> {
    pub l: u16,
    pub extensions: ServerExtensionsExtensions<'a>,
}
pub type ServerExtensionsInner<'a> = (u16, ServerExtensionsExtensions<'a>);
impl View for ServerExtensions<'_> {
    type V = SpecServerExtensions;
    open spec fn view(&self) -> Self::V {
        SpecServerExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ServerExtensions<'a>> for ServerExtensionsInner<'a> {
    fn ex_from(m: ServerExtensions<'a>) -> ServerExtensionsInner<'a> {
        (m.l, m.extensions)
    }
}
impl<'a> From<ServerExtensionsInner<'a>> for ServerExtensions<'a> {
    fn ex_from(m: ServerExtensionsInner<'a>) -> ServerExtensions<'a> {
        let (l, extensions) = m;
        ServerExtensions {
            l,
            extensions,
        }
    }
}
pub struct ServerExtensionsMapper;
impl View for ServerExtensionsMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerExtensionsMapper {
    type Src = SpecServerExtensionsInner;
    type Dst = SpecServerExtensions;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerExtensionsMapper {
    type Src<'a> = ServerExtensionsInner<'a>;
    type Dst<'a> = ServerExtensions<'a>;
    type SrcOwned = ServerExtensionsOwnedInner;
    type DstOwned = ServerExtensionsOwned;
}
pub struct ServerExtensionsOwned {
    pub l: u16,
    pub extensions: ServerExtensionsExtensionsOwned,
}
pub type ServerExtensionsOwnedInner = (u16, ServerExtensionsExtensionsOwned);
impl View for ServerExtensionsOwned {
    type V = SpecServerExtensions;
    open spec fn view(&self) -> Self::V {
        SpecServerExtensions {
            l: self.l@,
            extensions: self.extensions@,
        }
    }
}
impl From<ServerExtensionsOwned> for ServerExtensionsOwnedInner {
    fn ex_from(m: ServerExtensionsOwned) -> ServerExtensionsOwnedInner {
        (m.l, m.extensions)
    }
}
impl From<ServerExtensionsOwnedInner> for ServerExtensionsOwned {
    fn ex_from(m: ServerExtensionsOwnedInner) -> ServerExtensionsOwned {
        let (l, extensions) = m;
        ServerExtensionsOwned {
            l,
            extensions,
        }
    }
}

pub struct SpecServerHello {
    pub legacy_version: SpecProtocolVersion,
    pub random: SpecRandom,
    pub legacy_session_id_echo: SpecSessionId,
    pub cipher_suite: SpecCipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: SpecServerExtensions,
}
pub type SpecServerHelloInner = (SpecProtocolVersion, (SpecRandom, (SpecSessionId, (SpecCipherSuite, (u8, SpecServerExtensions)))));
impl SpecFrom<SpecServerHello> for SpecServerHelloInner {
    open spec fn spec_from(m: SpecServerHello) -> SpecServerHelloInner {
        (m.legacy_version, (m.random, (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))))
    }
}
impl SpecFrom<SpecServerHelloInner> for SpecServerHello {
    open spec fn spec_from(m: SpecServerHelloInner) -> SpecServerHello {
        let (legacy_version, (random, (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))))) = m;
        SpecServerHello {
            legacy_version,
            random,
            legacy_session_id_echo,
            cipher_suite,
            legacy_compression_method,
            extensions,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerHello<'a> {
    pub legacy_version: ProtocolVersion,
    pub random: Random<'a>,
    pub legacy_session_id_echo: SessionId<'a>,
    pub cipher_suite: CipherSuite,
    pub legacy_compression_method: u8,
    pub extensions: ServerExtensions<'a>,
}
pub type ServerHelloInner<'a> = (ProtocolVersion, (Random<'a>, (SessionId<'a>, (CipherSuite, (u8, ServerExtensions<'a>)))));
impl View for ServerHello<'_> {
    type V = SpecServerHello;
    open spec fn view(&self) -> Self::V {
        SpecServerHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id_echo: self.legacy_session_id_echo@,
            cipher_suite: self.cipher_suite@,
            legacy_compression_method: self.legacy_compression_method@,
            extensions: self.extensions@,
        }
    }
}
impl<'a> From<ServerHello<'a>> for ServerHelloInner<'a> {
    fn ex_from(m: ServerHello<'a>) -> ServerHelloInner<'a> {
        (m.legacy_version, (m.random, (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))))
    }
}
impl<'a> From<ServerHelloInner<'a>> for ServerHello<'a> {
    fn ex_from(m: ServerHelloInner<'a>) -> ServerHello<'a> {
        let (legacy_version, (random, (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))))) = m;
        ServerHello {
            legacy_version,
            random,
            legacy_session_id_echo,
            cipher_suite,
            legacy_compression_method,
            extensions,
        }
    }
}
pub struct ServerHelloMapper;
impl View for ServerHelloMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerHelloMapper {
    type Src = SpecServerHelloInner;
    type Dst = SpecServerHello;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerHelloMapper {
    type Src<'a> = ServerHelloInner<'a>;
    type Dst<'a> = ServerHello<'a>;
    type SrcOwned = ServerHelloOwnedInner;
    type DstOwned = ServerHelloOwned;
}
pub struct ServerHelloOwned {
    pub legacy_version: ProtocolVersionOwned,
    pub random: RandomOwned,
    pub legacy_session_id_echo: SessionIdOwned,
    pub cipher_suite: CipherSuiteOwned,
    pub legacy_compression_method: u8,
    pub extensions: ServerExtensionsOwned,
}
pub type ServerHelloOwnedInner = (ProtocolVersionOwned, (RandomOwned, (SessionIdOwned, (CipherSuiteOwned, (u8, ServerExtensionsOwned)))));
impl View for ServerHelloOwned {
    type V = SpecServerHello;
    open spec fn view(&self) -> Self::V {
        SpecServerHello {
            legacy_version: self.legacy_version@,
            random: self.random@,
            legacy_session_id_echo: self.legacy_session_id_echo@,
            cipher_suite: self.cipher_suite@,
            legacy_compression_method: self.legacy_compression_method@,
            extensions: self.extensions@,
        }
    }
}
impl From<ServerHelloOwned> for ServerHelloOwnedInner {
    fn ex_from(m: ServerHelloOwned) -> ServerHelloOwnedInner {
        (m.legacy_version, (m.random, (m.legacy_session_id_echo, (m.cipher_suite, (m.legacy_compression_method, m.extensions)))))
    }
}
impl From<ServerHelloOwnedInner> for ServerHelloOwned {
    fn ex_from(m: ServerHelloOwnedInner) -> ServerHelloOwned {
        let (legacy_version, (random, (legacy_session_id_echo, (cipher_suite, (legacy_compression_method, extensions))))) = m;
        ServerHelloOwned {
            legacy_version,
            random,
            legacy_session_id_echo,
            cipher_suite,
            legacy_compression_method,
            extensions,
        }
    }
}

pub type SpecFinished = Seq<u8>;
pub type Finished<'a> = &'a [u8];
pub type FinishedOwned = Vec<u8>;

pub enum SpecHandshakeMsg {
    ClientHello(SpecClientHello),
    ServerHello(SpecServerHello),
    NewSessionTicket(SpecNewSessionTicket),
    EndOfEarlyData(SpecEmpty),
    EncryptedExtensions(SpecEncryptedExtensions),
    Certificate(SpecCertificate),
    CertificateRequest(SpecCertificateRequest),
    CertificateVerify(SpecCertificateVerify),
    Finished(SpecFinished),
    KeyUpdate(SpecKeyUpdate),
}
pub type SpecHandshakeMsgInner = Either<SpecClientHello, Either<SpecServerHello, Either<SpecNewSessionTicket, Either<SpecEmpty, Either<SpecEncryptedExtensions, Either<SpecCertificate, Either<SpecCertificateRequest, Either<SpecCertificateVerify, Either<SpecFinished, SpecKeyUpdate>>>>>>>>>;
impl SpecFrom<SpecHandshakeMsg> for SpecHandshakeMsgInner {
    open spec fn spec_from(m: SpecHandshakeMsg) -> SpecHandshakeMsgInner {
        match m {
            SpecHandshakeMsg::ClientHello(m) => Either::Left(m),
            SpecHandshakeMsg::ServerHello(m) => Either::Right(Either::Left(m)),
            SpecHandshakeMsg::NewSessionTicket(m) => Either::Right(Either::Right(Either::Left(m))),
            SpecHandshakeMsg::EndOfEarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            SpecHandshakeMsg::EncryptedExtensions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            SpecHandshakeMsg::Certificate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            SpecHandshakeMsg::CertificateRequest(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            SpecHandshakeMsg::CertificateVerify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            SpecHandshakeMsg::Finished(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            SpecHandshakeMsg::KeyUpdate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }
}
impl SpecFrom<SpecHandshakeMsgInner> for SpecHandshakeMsg {
    open spec fn spec_from(m: SpecHandshakeMsgInner) -> SpecHandshakeMsg {
        match m {
            Either::Left(m) => SpecHandshakeMsg::ClientHello(m),
            Either::Right(Either::Left(m)) => SpecHandshakeMsg::ServerHello(m),
            Either::Right(Either::Right(Either::Left(m))) => SpecHandshakeMsg::NewSessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => SpecHandshakeMsg::EndOfEarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => SpecHandshakeMsg::EncryptedExtensions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => SpecHandshakeMsg::Certificate(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => SpecHandshakeMsg::CertificateRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => SpecHandshakeMsg::CertificateVerify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => SpecHandshakeMsg::Finished(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => SpecHandshakeMsg::KeyUpdate(m),
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HandshakeMsg<'a> {
    ClientHello(ClientHello<'a>),
    ServerHello(ServerHello<'a>),
    NewSessionTicket(NewSessionTicket<'a>),
    EndOfEarlyData(Empty<'a>),
    EncryptedExtensions(EncryptedExtensions<'a>),
    Certificate(Certificate<'a>),
    CertificateRequest(CertificateRequest<'a>),
    CertificateVerify(CertificateVerify<'a>),
    Finished(Finished<'a>),
    KeyUpdate(KeyUpdate),
}
pub type HandshakeMsgInner<'a> = Either<ClientHello<'a>, Either<ServerHello<'a>, Either<NewSessionTicket<'a>, Either<Empty<'a>, Either<EncryptedExtensions<'a>, Either<Certificate<'a>, Either<CertificateRequest<'a>, Either<CertificateVerify<'a>, Either<Finished<'a>, KeyUpdate>>>>>>>>>;
impl View for HandshakeMsg<'_> {
    type V = SpecHandshakeMsg;
    open spec fn view(&self) -> Self::V {
        match self {
            HandshakeMsg::ClientHello(m) => SpecHandshakeMsg::ClientHello(m@),
            HandshakeMsg::ServerHello(m) => SpecHandshakeMsg::ServerHello(m@),
            HandshakeMsg::NewSessionTicket(m) => SpecHandshakeMsg::NewSessionTicket(m@),
            HandshakeMsg::EndOfEarlyData(m) => SpecHandshakeMsg::EndOfEarlyData(m@),
            HandshakeMsg::EncryptedExtensions(m) => SpecHandshakeMsg::EncryptedExtensions(m@),
            HandshakeMsg::Certificate(m) => SpecHandshakeMsg::Certificate(m@),
            HandshakeMsg::CertificateRequest(m) => SpecHandshakeMsg::CertificateRequest(m@),
            HandshakeMsg::CertificateVerify(m) => SpecHandshakeMsg::CertificateVerify(m@),
            HandshakeMsg::Finished(m) => SpecHandshakeMsg::Finished(m@),
            HandshakeMsg::KeyUpdate(m) => SpecHandshakeMsg::KeyUpdate(m@),
        }
    }
}
impl<'a> From<HandshakeMsg<'a>> for HandshakeMsgInner<'a> {
    fn ex_from(m: HandshakeMsg<'a>) -> HandshakeMsgInner<'a> {
        match m {
            HandshakeMsg::ClientHello(m) => Either::Left(m),
            HandshakeMsg::ServerHello(m) => Either::Right(Either::Left(m)),
            HandshakeMsg::NewSessionTicket(m) => Either::Right(Either::Right(Either::Left(m))),
            HandshakeMsg::EndOfEarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            HandshakeMsg::EncryptedExtensions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            HandshakeMsg::Certificate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            HandshakeMsg::CertificateRequest(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            HandshakeMsg::CertificateVerify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            HandshakeMsg::Finished(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            HandshakeMsg::KeyUpdate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }
}
impl<'a> From<HandshakeMsgInner<'a>> for HandshakeMsg<'a> {
    fn ex_from(m: HandshakeMsgInner<'a>) -> HandshakeMsg<'a> {
        match m {
            Either::Left(m) => HandshakeMsg::ClientHello(m),
            Either::Right(Either::Left(m)) => HandshakeMsg::ServerHello(m),
            Either::Right(Either::Right(Either::Left(m))) => HandshakeMsg::NewSessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => HandshakeMsg::EndOfEarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => HandshakeMsg::EncryptedExtensions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => HandshakeMsg::Certificate(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => HandshakeMsg::CertificateRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => HandshakeMsg::CertificateVerify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => HandshakeMsg::Finished(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => HandshakeMsg::KeyUpdate(m),
        }
    }
}
pub struct HandshakeMsgMapper;
impl View for HandshakeMsgMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMsgMapper {
    type Src = SpecHandshakeMsgInner;
    type Dst = SpecHandshakeMsg;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for HandshakeMsgMapper {
    type Src<'a> = HandshakeMsgInner<'a>;
    type Dst<'a> = HandshakeMsg<'a>;
    type SrcOwned = HandshakeMsgOwnedInner;
    type DstOwned = HandshakeMsgOwned;
}
pub enum HandshakeMsgOwned {
    ClientHello(ClientHelloOwned),
    ServerHello(ServerHelloOwned),
    NewSessionTicket(NewSessionTicketOwned),
    EndOfEarlyData(EmptyOwned),
    EncryptedExtensions(EncryptedExtensionsOwned),
    Certificate(CertificateOwned),
    CertificateRequest(CertificateRequestOwned),
    CertificateVerify(CertificateVerifyOwned),
    Finished(FinishedOwned),
    KeyUpdate(KeyUpdateOwned),
}
pub type HandshakeMsgOwnedInner = Either<ClientHelloOwned, Either<ServerHelloOwned, Either<NewSessionTicketOwned, Either<EmptyOwned, Either<EncryptedExtensionsOwned, Either<CertificateOwned, Either<CertificateRequestOwned, Either<CertificateVerifyOwned, Either<FinishedOwned, KeyUpdateOwned>>>>>>>>>;
impl View for HandshakeMsgOwned {
    type V = SpecHandshakeMsg;
    open spec fn view(&self) -> Self::V {
        match self {
            HandshakeMsgOwned::ClientHello(m) => SpecHandshakeMsg::ClientHello(m@),
            HandshakeMsgOwned::ServerHello(m) => SpecHandshakeMsg::ServerHello(m@),
            HandshakeMsgOwned::NewSessionTicket(m) => SpecHandshakeMsg::NewSessionTicket(m@),
            HandshakeMsgOwned::EndOfEarlyData(m) => SpecHandshakeMsg::EndOfEarlyData(m@),
            HandshakeMsgOwned::EncryptedExtensions(m) => SpecHandshakeMsg::EncryptedExtensions(m@),
            HandshakeMsgOwned::Certificate(m) => SpecHandshakeMsg::Certificate(m@),
            HandshakeMsgOwned::CertificateRequest(m) => SpecHandshakeMsg::CertificateRequest(m@),
            HandshakeMsgOwned::CertificateVerify(m) => SpecHandshakeMsg::CertificateVerify(m@),
            HandshakeMsgOwned::Finished(m) => SpecHandshakeMsg::Finished(m@),
            HandshakeMsgOwned::KeyUpdate(m) => SpecHandshakeMsg::KeyUpdate(m@),
        }
    }
}
impl From<HandshakeMsgOwned> for HandshakeMsgOwnedInner {
    fn ex_from(m: HandshakeMsgOwned) -> HandshakeMsgOwnedInner {
        match m {
            HandshakeMsgOwned::ClientHello(m) => Either::Left(m),
            HandshakeMsgOwned::ServerHello(m) => Either::Right(Either::Left(m)),
            HandshakeMsgOwned::NewSessionTicket(m) => Either::Right(Either::Right(Either::Left(m))),
            HandshakeMsgOwned::EndOfEarlyData(m) => Either::Right(Either::Right(Either::Right(Either::Left(m)))),
            HandshakeMsgOwned::EncryptedExtensions(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))),
            HandshakeMsgOwned::Certificate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))),
            HandshakeMsgOwned::CertificateRequest(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))),
            HandshakeMsgOwned::CertificateVerify(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))),
            HandshakeMsgOwned::Finished(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))),
            HandshakeMsgOwned::KeyUpdate(m) => Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))),
        }
    }
}
impl From<HandshakeMsgOwnedInner> for HandshakeMsgOwned {
    fn ex_from(m: HandshakeMsgOwnedInner) -> HandshakeMsgOwned {
        match m {
            Either::Left(m) => HandshakeMsgOwned::ClientHello(m),
            Either::Right(Either::Left(m)) => HandshakeMsgOwned::ServerHello(m),
            Either::Right(Either::Right(Either::Left(m))) => HandshakeMsgOwned::NewSessionTicket(m),
            Either::Right(Either::Right(Either::Right(Either::Left(m)))) => HandshakeMsgOwned::EndOfEarlyData(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))) => HandshakeMsgOwned::EncryptedExtensions(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))) => HandshakeMsgOwned::Certificate(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))) => HandshakeMsgOwned::CertificateRequest(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m)))))))) => HandshakeMsgOwned::CertificateVerify(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Left(m))))))))) => HandshakeMsgOwned::Finished(m),
            Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(Either::Right(m))))))))) => HandshakeMsgOwned::KeyUpdate(m),
        }
    }
}

pub struct SpecHandshake {
    pub msg_type: SpecHandshakeType,
    pub length: u24,
    pub msg: SpecHandshakeMsg,
}
pub type SpecHandshakeInner = ((SpecHandshakeType, u24), SpecHandshakeMsg);
impl SpecFrom<SpecHandshake> for SpecHandshakeInner {
    open spec fn spec_from(m: SpecHandshake) -> SpecHandshakeInner {
        ((m.msg_type, m.length), m.msg)
    }
}
impl SpecFrom<SpecHandshakeInner> for SpecHandshake {
    open spec fn spec_from(m: SpecHandshakeInner) -> SpecHandshake {
        let ((msg_type, length), msg) = m;
        SpecHandshake {
            msg_type,
            length,
            msg,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Handshake<'a> {
    pub msg_type: HandshakeType,
    pub length: u24,
    pub msg: HandshakeMsg<'a>,
}
pub type HandshakeInner<'a> = ((HandshakeType, u24), HandshakeMsg<'a>);
impl View for Handshake<'_> {
    type V = SpecHandshake;
    open spec fn view(&self) -> Self::V {
        SpecHandshake {
            msg_type: self.msg_type@,
            length: self.length@,
            msg: self.msg@,
        }
    }
}
impl<'a> From<Handshake<'a>> for HandshakeInner<'a> {
    fn ex_from(m: Handshake<'a>) -> HandshakeInner<'a> {
        ((m.msg_type, m.length), m.msg)
    }
}
impl<'a> From<HandshakeInner<'a>> for Handshake<'a> {
    fn ex_from(m: HandshakeInner<'a>) -> Handshake<'a> {
        let ((msg_type, length), msg) = m;
        Handshake {
            msg_type,
            length,
            msg,
        }
    }
}
pub struct HandshakeMapper;
impl View for HandshakeMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HandshakeMapper {
    type Src = SpecHandshakeInner;
    type Dst = SpecHandshake;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for HandshakeMapper {
    type Src<'a> = HandshakeInner<'a>;
    type Dst<'a> = Handshake<'a>;
    type SrcOwned = HandshakeOwnedInner;
    type DstOwned = HandshakeOwned;
}
pub struct HandshakeOwned {
    pub msg_type: HandshakeTypeOwned,
    pub length: u24,
    pub msg: HandshakeMsgOwned,
}
pub type HandshakeOwnedInner = ((HandshakeTypeOwned, u24), HandshakeMsgOwned);
impl View for HandshakeOwned {
    type V = SpecHandshake;
    open spec fn view(&self) -> Self::V {
        SpecHandshake {
            msg_type: self.msg_type@,
            length: self.length@,
            msg: self.msg@,
        }
    }
}
impl From<HandshakeOwned> for HandshakeOwnedInner {
    fn ex_from(m: HandshakeOwned) -> HandshakeOwnedInner {
        ((m.msg_type, m.length), m.msg)
    }
}
impl From<HandshakeOwnedInner> for HandshakeOwned {
    fn ex_from(m: HandshakeOwnedInner) -> HandshakeOwned {
        let ((msg_type, length), msg) = m;
        HandshakeOwned {
            msg_type,
            length,
            msg,
        }
    }
}

pub struct SpecServerCertTypeServerExtension {
    pub server_certificate_type: SpecCertificateType,
}
pub type SpecServerCertTypeServerExtensionInner = SpecCertificateType;
impl SpecFrom<SpecServerCertTypeServerExtension> for SpecServerCertTypeServerExtensionInner {
    open spec fn spec_from(m: SpecServerCertTypeServerExtension) -> SpecServerCertTypeServerExtensionInner {
        m.server_certificate_type
    }
}
impl SpecFrom<SpecServerCertTypeServerExtensionInner> for SpecServerCertTypeServerExtension {
    open spec fn spec_from(m: SpecServerCertTypeServerExtensionInner) -> SpecServerCertTypeServerExtension {
        let server_certificate_type = m;
        SpecServerCertTypeServerExtension {
            server_certificate_type,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerCertTypeServerExtension {
    pub server_certificate_type: CertificateType,
}
pub type ServerCertTypeServerExtensionInner = CertificateType;
impl View for ServerCertTypeServerExtension {
    type V = SpecServerCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeServerExtension {
            server_certificate_type: self.server_certificate_type@,
        }
    }
}
impl From<ServerCertTypeServerExtension> for ServerCertTypeServerExtensionInner {
    fn ex_from(m: ServerCertTypeServerExtension) -> ServerCertTypeServerExtensionInner {
        m.server_certificate_type
    }
}
impl From<ServerCertTypeServerExtensionInner> for ServerCertTypeServerExtension {
    fn ex_from(m: ServerCertTypeServerExtensionInner) -> ServerCertTypeServerExtension {
        let server_certificate_type = m;
        ServerCertTypeServerExtension {
            server_certificate_type,
        }
    }
}
pub struct ServerCertTypeServerExtensionMapper;
impl View for ServerCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ServerCertTypeServerExtensionMapper {
    type Src = SpecServerCertTypeServerExtensionInner;
    type Dst = SpecServerCertTypeServerExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ServerCertTypeServerExtensionMapper {
    type Src<'a> = ServerCertTypeServerExtensionInner;
    type Dst<'a> = ServerCertTypeServerExtension;
    type SrcOwned = ServerCertTypeServerExtensionOwnedInner;
    type DstOwned = ServerCertTypeServerExtensionOwned;
}
pub struct ServerCertTypeServerExtensionOwned {
    pub server_certificate_type: CertificateTypeOwned,
}
pub type ServerCertTypeServerExtensionOwnedInner = CertificateTypeOwned;
impl View for ServerCertTypeServerExtensionOwned {
    type V = SpecServerCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecServerCertTypeServerExtension {
            server_certificate_type: self.server_certificate_type@,
        }
    }
}
impl From<ServerCertTypeServerExtensionOwned> for ServerCertTypeServerExtensionOwnedInner {
    fn ex_from(m: ServerCertTypeServerExtensionOwned) -> ServerCertTypeServerExtensionOwnedInner {
        m.server_certificate_type
    }
}
impl From<ServerCertTypeServerExtensionOwnedInner> for ServerCertTypeServerExtensionOwned {
    fn ex_from(m: ServerCertTypeServerExtensionOwnedInner) -> ServerCertTypeServerExtensionOwned {
        let server_certificate_type = m;
        ServerCertTypeServerExtensionOwned {
            server_certificate_type,
        }
    }
}

pub struct SpecOpaque2Ffff {
    pub l: SpecUint2Ffff,
    pub data: Seq<u8>,
}
pub type SpecOpaque2FfffInner = (SpecUint2Ffff, Seq<u8>);
impl SpecFrom<SpecOpaque2Ffff> for SpecOpaque2FfffInner {
    open spec fn spec_from(m: SpecOpaque2Ffff) -> SpecOpaque2FfffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque2FfffInner> for SpecOpaque2Ffff {
    open spec fn spec_from(m: SpecOpaque2FfffInner) -> SpecOpaque2Ffff {
        let (l, data) = m;
        SpecOpaque2Ffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque2Ffff<'a> {
    pub l: Uint2Ffff,
    pub data: &'a [u8],
}
pub type Opaque2FfffInner<'a> = (Uint2Ffff, &'a [u8]);
impl View for Opaque2Ffff<'_> {
    type V = SpecOpaque2Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque2Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque2Ffff<'a>> for Opaque2FfffInner<'a> {
    fn ex_from(m: Opaque2Ffff<'a>) -> Opaque2FfffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque2FfffInner<'a>> for Opaque2Ffff<'a> {
    fn ex_from(m: Opaque2FfffInner<'a>) -> Opaque2Ffff<'a> {
        let (l, data) = m;
        Opaque2Ffff {
            l,
            data,
        }
    }
}
pub struct Opaque2FfffMapper;
impl View for Opaque2FfffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque2FfffMapper {
    type Src = SpecOpaque2FfffInner;
    type Dst = SpecOpaque2Ffff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque2FfffMapper {
    type Src<'a> = Opaque2FfffInner<'a>;
    type Dst<'a> = Opaque2Ffff<'a>;
    type SrcOwned = Opaque2FfffOwnedInner;
    type DstOwned = Opaque2FfffOwned;
}
pub struct Opaque2FfffOwned {
    pub l: Uint2FfffOwned,
    pub data: Vec<u8>,
}
pub type Opaque2FfffOwnedInner = (Uint2FfffOwned, Vec<u8>);
impl View for Opaque2FfffOwned {
    type V = SpecOpaque2Ffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque2Ffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque2FfffOwned> for Opaque2FfffOwnedInner {
    fn ex_from(m: Opaque2FfffOwned) -> Opaque2FfffOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque2FfffOwnedInner> for Opaque2FfffOwned {
    fn ex_from(m: Opaque2FfffOwnedInner) -> Opaque2FfffOwned {
        let (l, data) = m;
        Opaque2FfffOwned {
            l,
            data,
        }
    }
}

pub type SpecOcspResponse = SpecOpaque1Ffffff;
pub type OcspResponse<'a> = Opaque1Ffffff<'a>;
pub type OcspResponseOwned = Opaque1FfffffOwned;

pub struct SpecCertificateStatus {
    pub status_type: u8,
    pub response: SpecOcspResponse,
}
pub type SpecCertificateStatusInner = (u8, SpecOcspResponse);
impl SpecFrom<SpecCertificateStatus> for SpecCertificateStatusInner {
    open spec fn spec_from(m: SpecCertificateStatus) -> SpecCertificateStatusInner {
        (m.status_type, m.response)
    }
}
impl SpecFrom<SpecCertificateStatusInner> for SpecCertificateStatus {
    open spec fn spec_from(m: SpecCertificateStatusInner) -> SpecCertificateStatus {
        let (status_type, response) = m;
        SpecCertificateStatus {
            status_type,
            response,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CertificateStatus<'a> {
    pub status_type: u8,
    pub response: OcspResponse<'a>,
}
pub type CertificateStatusInner<'a> = (u8, OcspResponse<'a>);
impl View for CertificateStatus<'_> {
    type V = SpecCertificateStatus;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatus {
            status_type: self.status_type@,
            response: self.response@,
        }
    }
}
impl<'a> From<CertificateStatus<'a>> for CertificateStatusInner<'a> {
    fn ex_from(m: CertificateStatus<'a>) -> CertificateStatusInner<'a> {
        (m.status_type, m.response)
    }
}
impl<'a> From<CertificateStatusInner<'a>> for CertificateStatus<'a> {
    fn ex_from(m: CertificateStatusInner<'a>) -> CertificateStatus<'a> {
        let (status_type, response) = m;
        CertificateStatus {
            status_type,
            response,
        }
    }
}
pub struct CertificateStatusMapper;
impl View for CertificateStatusMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for CertificateStatusMapper {
    type Src = SpecCertificateStatusInner;
    type Dst = SpecCertificateStatus;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for CertificateStatusMapper {
    type Src<'a> = CertificateStatusInner<'a>;
    type Dst<'a> = CertificateStatus<'a>;
    type SrcOwned = CertificateStatusOwnedInner;
    type DstOwned = CertificateStatusOwned;
}
pub struct CertificateStatusOwned {
    pub status_type: u8,
    pub response: OcspResponseOwned,
}
pub type CertificateStatusOwnedInner = (u8, OcspResponseOwned);
impl View for CertificateStatusOwned {
    type V = SpecCertificateStatus;
    open spec fn view(&self) -> Self::V {
        SpecCertificateStatus {
            status_type: self.status_type@,
            response: self.response@,
        }
    }
}
impl From<CertificateStatusOwned> for CertificateStatusOwnedInner {
    fn ex_from(m: CertificateStatusOwned) -> CertificateStatusOwnedInner {
        (m.status_type, m.response)
    }
}
impl From<CertificateStatusOwnedInner> for CertificateStatusOwned {
    fn ex_from(m: CertificateStatusOwnedInner) -> CertificateStatusOwned {
        let (status_type, response) = m;
        CertificateStatusOwned {
            status_type,
            response,
        }
    }
}

pub struct SpecHeartbeatExtension {
    pub mode: SpecHeartbeatMode,
}
pub type SpecHeartbeatExtensionInner = SpecHeartbeatMode;
impl SpecFrom<SpecHeartbeatExtension> for SpecHeartbeatExtensionInner {
    open spec fn spec_from(m: SpecHeartbeatExtension) -> SpecHeartbeatExtensionInner {
        m.mode
    }
}
impl SpecFrom<SpecHeartbeatExtensionInner> for SpecHeartbeatExtension {
    open spec fn spec_from(m: SpecHeartbeatExtensionInner) -> SpecHeartbeatExtension {
        let mode = m;
        SpecHeartbeatExtension {
            mode,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeartbeatExtension {
    pub mode: HeartbeatMode,
}
pub type HeartbeatExtensionInner = HeartbeatMode;
impl View for HeartbeatExtension {
    type V = SpecHeartbeatExtension;
    open spec fn view(&self) -> Self::V {
        SpecHeartbeatExtension {
            mode: self.mode@,
        }
    }
}
impl From<HeartbeatExtension> for HeartbeatExtensionInner {
    fn ex_from(m: HeartbeatExtension) -> HeartbeatExtensionInner {
        m.mode
    }
}
impl From<HeartbeatExtensionInner> for HeartbeatExtension {
    fn ex_from(m: HeartbeatExtensionInner) -> HeartbeatExtension {
        let mode = m;
        HeartbeatExtension {
            mode,
        }
    }
}
pub struct HeartbeatExtensionMapper;
impl View for HeartbeatExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for HeartbeatExtensionMapper {
    type Src = SpecHeartbeatExtensionInner;
    type Dst = SpecHeartbeatExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for HeartbeatExtensionMapper {
    type Src<'a> = HeartbeatExtensionInner;
    type Dst<'a> = HeartbeatExtension;
    type SrcOwned = HeartbeatExtensionOwnedInner;
    type DstOwned = HeartbeatExtensionOwned;
}
pub struct HeartbeatExtensionOwned {
    pub mode: HeartbeatModeOwned,
}
pub type HeartbeatExtensionOwnedInner = HeartbeatModeOwned;
impl View for HeartbeatExtensionOwned {
    type V = SpecHeartbeatExtension;
    open spec fn view(&self) -> Self::V {
        SpecHeartbeatExtension {
            mode: self.mode@,
        }
    }
}
impl From<HeartbeatExtensionOwned> for HeartbeatExtensionOwnedInner {
    fn ex_from(m: HeartbeatExtensionOwned) -> HeartbeatExtensionOwnedInner {
        m.mode
    }
}
impl From<HeartbeatExtensionOwnedInner> for HeartbeatExtensionOwned {
    fn ex_from(m: HeartbeatExtensionOwnedInner) -> HeartbeatExtensionOwned {
        let mode = m;
        HeartbeatExtensionOwned {
            mode,
        }
    }
}


#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AlertLevel {
    Warning = 1,
Fatal = 2
}
pub type SpecAlertLevel = AlertLevel;
pub type AlertLevelOwned = AlertLevel;

pub type AlertLevelInner = u8;

impl View for AlertLevel {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AlertLevelInner> for AlertLevel {
    type Error = ();

    open spec fn spec_try_from(v: AlertLevelInner) -> Result<AlertLevel, ()> {
        match v {
            1u8 => Ok(AlertLevel::Warning),
            2u8 => Ok(AlertLevel::Fatal),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AlertLevel> for AlertLevelInner {
    type Error = ();

    open spec fn spec_try_from(v: AlertLevel) -> Result<AlertLevelInner, ()> {
        match v {
            AlertLevel::Warning => Ok(1u8),
            AlertLevel::Fatal => Ok(2u8),
        }
    }
}

impl TryFrom<AlertLevelInner> for AlertLevel {
    type Error = ();

    fn ex_try_from(v: AlertLevelInner) -> Result<AlertLevel, ()> {
        match v {
            1u8 => Ok(AlertLevel::Warning),
            2u8 => Ok(AlertLevel::Fatal),
            _ => Err(()),
        }
    }
}

impl TryFrom<AlertLevel> for AlertLevelInner {
    type Error = ();

    fn ex_try_from(v: AlertLevel) -> Result<AlertLevelInner, ()> {
        match v {
            AlertLevel::Warning => Ok(1u8),
            AlertLevel::Fatal => Ok(2u8),
        }
    }
}

pub struct AlertLevelMapper;

impl View for AlertLevelMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for AlertLevelMapper {
    type Src = AlertLevelInner;
    type Dst = AlertLevel;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for AlertLevelMapper {
    type Src<'a> = AlertLevelInner;
    type Dst<'a> = AlertLevel;

    type SrcOwned = AlertLevelInner;
    type DstOwned = AlertLevel;
}

pub type SpecUnknownExtension = SpecOpaque0Ffff;
pub type UnknownExtension<'a> = Opaque0Ffff<'a>;
pub type UnknownExtensionOwned = Opaque0FfffOwned;


#[derive(Structural, Debug, Copy, Clone, PartialEq, Eq)]
pub enum AlertDescription {
    CloseNotify = 0,
UnexpectedMessage = 10,
BadRecordMac = 20,
RecordOverflow = 22,
HandshakeFailure = 40,
BadCertificate = 42,
UnsupportedCertificate = 43,
CertificateRevoked = 44,
CertificateExpired = 45,
CertificateUnknown = 46,
IllegalParameter = 47,
UnknownCA = 48,
AccessDenied = 49,
DecodeError = 50,
DecryptError = 51,
ProtocolVersion = 70,
InsufficientSecurity = 71,
InternalError = 80,
InappropriateFallback = 86,
UserCanceled = 90,
MissingExtension = 109,
UnsupportedExtension = 110,
UnrecognizedName = 112,
BadCertificateStatusResponse = 113,
UnknownPSKIdentity = 115,
CertificateRequired = 116,
NoApplicationProtocol = 120
}
pub type SpecAlertDescription = AlertDescription;
pub type AlertDescriptionOwned = AlertDescription;

pub type AlertDescriptionInner = u8;

impl View for AlertDescription {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFrom<AlertDescriptionInner> for AlertDescription {
    type Error = ();

    open spec fn spec_try_from(v: AlertDescriptionInner) -> Result<AlertDescription, ()> {
        match v {
            0u8 => Ok(AlertDescription::CloseNotify),
            10u8 => Ok(AlertDescription::UnexpectedMessage),
            20u8 => Ok(AlertDescription::BadRecordMac),
            22u8 => Ok(AlertDescription::RecordOverflow),
            40u8 => Ok(AlertDescription::HandshakeFailure),
            42u8 => Ok(AlertDescription::BadCertificate),
            43u8 => Ok(AlertDescription::UnsupportedCertificate),
            44u8 => Ok(AlertDescription::CertificateRevoked),
            45u8 => Ok(AlertDescription::CertificateExpired),
            46u8 => Ok(AlertDescription::CertificateUnknown),
            47u8 => Ok(AlertDescription::IllegalParameter),
            48u8 => Ok(AlertDescription::UnknownCA),
            49u8 => Ok(AlertDescription::AccessDenied),
            50u8 => Ok(AlertDescription::DecodeError),
            51u8 => Ok(AlertDescription::DecryptError),
            70u8 => Ok(AlertDescription::ProtocolVersion),
            71u8 => Ok(AlertDescription::InsufficientSecurity),
            80u8 => Ok(AlertDescription::InternalError),
            86u8 => Ok(AlertDescription::InappropriateFallback),
            90u8 => Ok(AlertDescription::UserCanceled),
            109u8 => Ok(AlertDescription::MissingExtension),
            110u8 => Ok(AlertDescription::UnsupportedExtension),
            112u8 => Ok(AlertDescription::UnrecognizedName),
            113u8 => Ok(AlertDescription::BadCertificateStatusResponse),
            115u8 => Ok(AlertDescription::UnknownPSKIdentity),
            116u8 => Ok(AlertDescription::CertificateRequired),
            120u8 => Ok(AlertDescription::NoApplicationProtocol),
            _ => Err(()),
        }
    }
}

impl SpecTryFrom<AlertDescription> for AlertDescriptionInner {
    type Error = ();

    open spec fn spec_try_from(v: AlertDescription) -> Result<AlertDescriptionInner, ()> {
        match v {
            AlertDescription::CloseNotify => Ok(0u8),
            AlertDescription::UnexpectedMessage => Ok(10u8),
            AlertDescription::BadRecordMac => Ok(20u8),
            AlertDescription::RecordOverflow => Ok(22u8),
            AlertDescription::HandshakeFailure => Ok(40u8),
            AlertDescription::BadCertificate => Ok(42u8),
            AlertDescription::UnsupportedCertificate => Ok(43u8),
            AlertDescription::CertificateRevoked => Ok(44u8),
            AlertDescription::CertificateExpired => Ok(45u8),
            AlertDescription::CertificateUnknown => Ok(46u8),
            AlertDescription::IllegalParameter => Ok(47u8),
            AlertDescription::UnknownCA => Ok(48u8),
            AlertDescription::AccessDenied => Ok(49u8),
            AlertDescription::DecodeError => Ok(50u8),
            AlertDescription::DecryptError => Ok(51u8),
            AlertDescription::ProtocolVersion => Ok(70u8),
            AlertDescription::InsufficientSecurity => Ok(71u8),
            AlertDescription::InternalError => Ok(80u8),
            AlertDescription::InappropriateFallback => Ok(86u8),
            AlertDescription::UserCanceled => Ok(90u8),
            AlertDescription::MissingExtension => Ok(109u8),
            AlertDescription::UnsupportedExtension => Ok(110u8),
            AlertDescription::UnrecognizedName => Ok(112u8),
            AlertDescription::BadCertificateStatusResponse => Ok(113u8),
            AlertDescription::UnknownPSKIdentity => Ok(115u8),
            AlertDescription::CertificateRequired => Ok(116u8),
            AlertDescription::NoApplicationProtocol => Ok(120u8),
        }
    }
}

impl TryFrom<AlertDescriptionInner> for AlertDescription {
    type Error = ();

    fn ex_try_from(v: AlertDescriptionInner) -> Result<AlertDescription, ()> {
        match v {
            0u8 => Ok(AlertDescription::CloseNotify),
            10u8 => Ok(AlertDescription::UnexpectedMessage),
            20u8 => Ok(AlertDescription::BadRecordMac),
            22u8 => Ok(AlertDescription::RecordOverflow),
            40u8 => Ok(AlertDescription::HandshakeFailure),
            42u8 => Ok(AlertDescription::BadCertificate),
            43u8 => Ok(AlertDescription::UnsupportedCertificate),
            44u8 => Ok(AlertDescription::CertificateRevoked),
            45u8 => Ok(AlertDescription::CertificateExpired),
            46u8 => Ok(AlertDescription::CertificateUnknown),
            47u8 => Ok(AlertDescription::IllegalParameter),
            48u8 => Ok(AlertDescription::UnknownCA),
            49u8 => Ok(AlertDescription::AccessDenied),
            50u8 => Ok(AlertDescription::DecodeError),
            51u8 => Ok(AlertDescription::DecryptError),
            70u8 => Ok(AlertDescription::ProtocolVersion),
            71u8 => Ok(AlertDescription::InsufficientSecurity),
            80u8 => Ok(AlertDescription::InternalError),
            86u8 => Ok(AlertDescription::InappropriateFallback),
            90u8 => Ok(AlertDescription::UserCanceled),
            109u8 => Ok(AlertDescription::MissingExtension),
            110u8 => Ok(AlertDescription::UnsupportedExtension),
            112u8 => Ok(AlertDescription::UnrecognizedName),
            113u8 => Ok(AlertDescription::BadCertificateStatusResponse),
            115u8 => Ok(AlertDescription::UnknownPSKIdentity),
            116u8 => Ok(AlertDescription::CertificateRequired),
            120u8 => Ok(AlertDescription::NoApplicationProtocol),
            _ => Err(()),
        }
    }
}

impl TryFrom<AlertDescription> for AlertDescriptionInner {
    type Error = ();

    fn ex_try_from(v: AlertDescription) -> Result<AlertDescriptionInner, ()> {
        match v {
            AlertDescription::CloseNotify => Ok(0u8),
            AlertDescription::UnexpectedMessage => Ok(10u8),
            AlertDescription::BadRecordMac => Ok(20u8),
            AlertDescription::RecordOverflow => Ok(22u8),
            AlertDescription::HandshakeFailure => Ok(40u8),
            AlertDescription::BadCertificate => Ok(42u8),
            AlertDescription::UnsupportedCertificate => Ok(43u8),
            AlertDescription::CertificateRevoked => Ok(44u8),
            AlertDescription::CertificateExpired => Ok(45u8),
            AlertDescription::CertificateUnknown => Ok(46u8),
            AlertDescription::IllegalParameter => Ok(47u8),
            AlertDescription::UnknownCA => Ok(48u8),
            AlertDescription::AccessDenied => Ok(49u8),
            AlertDescription::DecodeError => Ok(50u8),
            AlertDescription::DecryptError => Ok(51u8),
            AlertDescription::ProtocolVersion => Ok(70u8),
            AlertDescription::InsufficientSecurity => Ok(71u8),
            AlertDescription::InternalError => Ok(80u8),
            AlertDescription::InappropriateFallback => Ok(86u8),
            AlertDescription::UserCanceled => Ok(90u8),
            AlertDescription::MissingExtension => Ok(109u8),
            AlertDescription::UnsupportedExtension => Ok(110u8),
            AlertDescription::UnrecognizedName => Ok(112u8),
            AlertDescription::BadCertificateStatusResponse => Ok(113u8),
            AlertDescription::UnknownPSKIdentity => Ok(115u8),
            AlertDescription::CertificateRequired => Ok(116u8),
            AlertDescription::NoApplicationProtocol => Ok(120u8),
        }
    }
}

pub struct AlertDescriptionMapper;

impl View for AlertDescriptionMapper {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecTryFromInto for AlertDescriptionMapper {
    type Src = AlertDescriptionInner;
    type Dst = AlertDescription;

    proof fn spec_iso(s: Self::Src) {}

    proof fn spec_iso_rev(s: Self::Dst) {}
}

impl TryFromInto for AlertDescriptionMapper {
    type Src<'a> = AlertDescriptionInner;
    type Dst<'a> = AlertDescription;

    type SrcOwned = AlertDescriptionInner;
    type DstOwned = AlertDescription;
}

pub struct SpecAlert {
    pub level: SpecAlertLevel,
    pub description: SpecAlertDescription,
}
pub type SpecAlertInner = (SpecAlertLevel, SpecAlertDescription);
impl SpecFrom<SpecAlert> for SpecAlertInner {
    open spec fn spec_from(m: SpecAlert) -> SpecAlertInner {
        (m.level, m.description)
    }
}
impl SpecFrom<SpecAlertInner> for SpecAlert {
    open spec fn spec_from(m: SpecAlertInner) -> SpecAlert {
        let (level, description) = m;
        SpecAlert {
            level,
            description,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Alert {
    pub level: AlertLevel,
    pub description: AlertDescription,
}
pub type AlertInner = (AlertLevel, AlertDescription);
impl View for Alert {
    type V = SpecAlert;
    open spec fn view(&self) -> Self::V {
        SpecAlert {
            level: self.level@,
            description: self.description@,
        }
    }
}
impl From<Alert> for AlertInner {
    fn ex_from(m: Alert) -> AlertInner {
        (m.level, m.description)
    }
}
impl From<AlertInner> for Alert {
    fn ex_from(m: AlertInner) -> Alert {
        let (level, description) = m;
        Alert {
            level,
            description,
        }
    }
}
pub struct AlertMapper;
impl View for AlertMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for AlertMapper {
    type Src = SpecAlertInner;
    type Dst = SpecAlert;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for AlertMapper {
    type Src<'a> = AlertInner;
    type Dst<'a> = Alert;
    type SrcOwned = AlertOwnedInner;
    type DstOwned = AlertOwned;
}
pub struct AlertOwned {
    pub level: AlertLevelOwned,
    pub description: AlertDescriptionOwned,
}
pub type AlertOwnedInner = (AlertLevelOwned, AlertDescriptionOwned);
impl View for AlertOwned {
    type V = SpecAlert;
    open spec fn view(&self) -> Self::V {
        SpecAlert {
            level: self.level@,
            description: self.description@,
        }
    }
}
impl From<AlertOwned> for AlertOwnedInner {
    fn ex_from(m: AlertOwned) -> AlertOwnedInner {
        (m.level, m.description)
    }
}
impl From<AlertOwnedInner> for AlertOwned {
    fn ex_from(m: AlertOwnedInner) -> AlertOwned {
        let (level, description) = m;
        AlertOwned {
            level,
            description,
        }
    }
}

pub struct SpecClientCertTypeServerExtension {
    pub client_certificate_type: SpecCertificateType,
}
pub type SpecClientCertTypeServerExtensionInner = SpecCertificateType;
impl SpecFrom<SpecClientCertTypeServerExtension> for SpecClientCertTypeServerExtensionInner {
    open spec fn spec_from(m: SpecClientCertTypeServerExtension) -> SpecClientCertTypeServerExtensionInner {
        m.client_certificate_type
    }
}
impl SpecFrom<SpecClientCertTypeServerExtensionInner> for SpecClientCertTypeServerExtension {
    open spec fn spec_from(m: SpecClientCertTypeServerExtensionInner) -> SpecClientCertTypeServerExtension {
        let client_certificate_type = m;
        SpecClientCertTypeServerExtension {
            client_certificate_type,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClientCertTypeServerExtension {
    pub client_certificate_type: CertificateType,
}
pub type ClientCertTypeServerExtensionInner = CertificateType;
impl View for ClientCertTypeServerExtension {
    type V = SpecClientCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeServerExtension {
            client_certificate_type: self.client_certificate_type@,
        }
    }
}
impl From<ClientCertTypeServerExtension> for ClientCertTypeServerExtensionInner {
    fn ex_from(m: ClientCertTypeServerExtension) -> ClientCertTypeServerExtensionInner {
        m.client_certificate_type
    }
}
impl From<ClientCertTypeServerExtensionInner> for ClientCertTypeServerExtension {
    fn ex_from(m: ClientCertTypeServerExtensionInner) -> ClientCertTypeServerExtension {
        let client_certificate_type = m;
        ClientCertTypeServerExtension {
            client_certificate_type,
        }
    }
}
pub struct ClientCertTypeServerExtensionMapper;
impl View for ClientCertTypeServerExtensionMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for ClientCertTypeServerExtensionMapper {
    type Src = SpecClientCertTypeServerExtensionInner;
    type Dst = SpecClientCertTypeServerExtension;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for ClientCertTypeServerExtensionMapper {
    type Src<'a> = ClientCertTypeServerExtensionInner;
    type Dst<'a> = ClientCertTypeServerExtension;
    type SrcOwned = ClientCertTypeServerExtensionOwnedInner;
    type DstOwned = ClientCertTypeServerExtensionOwned;
}
pub struct ClientCertTypeServerExtensionOwned {
    pub client_certificate_type: CertificateTypeOwned,
}
pub type ClientCertTypeServerExtensionOwnedInner = CertificateTypeOwned;
impl View for ClientCertTypeServerExtensionOwned {
    type V = SpecClientCertTypeServerExtension;
    open spec fn view(&self) -> Self::V {
        SpecClientCertTypeServerExtension {
            client_certificate_type: self.client_certificate_type@,
        }
    }
}
impl From<ClientCertTypeServerExtensionOwned> for ClientCertTypeServerExtensionOwnedInner {
    fn ex_from(m: ClientCertTypeServerExtensionOwned) -> ClientCertTypeServerExtensionOwnedInner {
        m.client_certificate_type
    }
}
impl From<ClientCertTypeServerExtensionOwnedInner> for ClientCertTypeServerExtensionOwned {
    fn ex_from(m: ClientCertTypeServerExtensionOwnedInner) -> ClientCertTypeServerExtensionOwned {
        let client_certificate_type = m;
        ClientCertTypeServerExtensionOwned {
            client_certificate_type,
        }
    }
}

pub struct SpecTlsCiphertext {
    pub opaque_type: SpecContentType,
    pub version: SpecProtocolVersion,
    pub encrypted_record: SpecOpaque0Ffff,
}
pub type SpecTlsCiphertextInner = (SpecContentType, (SpecProtocolVersion, SpecOpaque0Ffff));
impl SpecFrom<SpecTlsCiphertext> for SpecTlsCiphertextInner {
    open spec fn spec_from(m: SpecTlsCiphertext) -> SpecTlsCiphertextInner {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl SpecFrom<SpecTlsCiphertextInner> for SpecTlsCiphertext {
    open spec fn spec_from(m: SpecTlsCiphertextInner) -> SpecTlsCiphertext {
        let (opaque_type, (version, encrypted_record)) = m;
        SpecTlsCiphertext {
            opaque_type,
            version,
            encrypted_record,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TlsCiphertext<'a> {
    pub opaque_type: ContentType,
    pub version: ProtocolVersion,
    pub encrypted_record: Opaque0Ffff<'a>,
}
pub type TlsCiphertextInner<'a> = (ContentType, (ProtocolVersion, Opaque0Ffff<'a>));
impl View for TlsCiphertext<'_> {
    type V = SpecTlsCiphertext;
    open spec fn view(&self) -> Self::V {
        SpecTlsCiphertext {
            opaque_type: self.opaque_type@,
            version: self.version@,
            encrypted_record: self.encrypted_record@,
        }
    }
}
impl<'a> From<TlsCiphertext<'a>> for TlsCiphertextInner<'a> {
    fn ex_from(m: TlsCiphertext<'a>) -> TlsCiphertextInner<'a> {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl<'a> From<TlsCiphertextInner<'a>> for TlsCiphertext<'a> {
    fn ex_from(m: TlsCiphertextInner<'a>) -> TlsCiphertext<'a> {
        let (opaque_type, (version, encrypted_record)) = m;
        TlsCiphertext {
            opaque_type,
            version,
            encrypted_record,
        }
    }
}
pub struct TlsCiphertextMapper;
impl View for TlsCiphertextMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for TlsCiphertextMapper {
    type Src = SpecTlsCiphertextInner;
    type Dst = SpecTlsCiphertext;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for TlsCiphertextMapper {
    type Src<'a> = TlsCiphertextInner<'a>;
    type Dst<'a> = TlsCiphertext<'a>;
    type SrcOwned = TlsCiphertextOwnedInner;
    type DstOwned = TlsCiphertextOwned;
}
pub struct TlsCiphertextOwned {
    pub opaque_type: ContentTypeOwned,
    pub version: ProtocolVersionOwned,
    pub encrypted_record: Opaque0FfffOwned,
}
pub type TlsCiphertextOwnedInner = (ContentTypeOwned, (ProtocolVersionOwned, Opaque0FfffOwned));
impl View for TlsCiphertextOwned {
    type V = SpecTlsCiphertext;
    open spec fn view(&self) -> Self::V {
        SpecTlsCiphertext {
            opaque_type: self.opaque_type@,
            version: self.version@,
            encrypted_record: self.encrypted_record@,
        }
    }
}
impl From<TlsCiphertextOwned> for TlsCiphertextOwnedInner {
    fn ex_from(m: TlsCiphertextOwned) -> TlsCiphertextOwnedInner {
        (m.opaque_type, (m.version, m.encrypted_record))
    }
}
impl From<TlsCiphertextOwnedInner> for TlsCiphertextOwned {
    fn ex_from(m: TlsCiphertextOwnedInner) -> TlsCiphertextOwned {
        let (opaque_type, (version, encrypted_record)) = m;
        TlsCiphertextOwned {
            opaque_type,
            version,
            encrypted_record,
        }
    }
}

pub struct SpecOpaque0Ffffff {
    pub l: u24,
    pub data: Seq<u8>,
}
pub type SpecOpaque0FfffffInner = (u24, Seq<u8>);
impl SpecFrom<SpecOpaque0Ffffff> for SpecOpaque0FfffffInner {
    open spec fn spec_from(m: SpecOpaque0Ffffff) -> SpecOpaque0FfffffInner {
        (m.l, m.data)
    }
}
impl SpecFrom<SpecOpaque0FfffffInner> for SpecOpaque0Ffffff {
    open spec fn spec_from(m: SpecOpaque0FfffffInner) -> SpecOpaque0Ffffff {
        let (l, data) = m;
        SpecOpaque0Ffffff {
            l,
            data,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opaque0Ffffff<'a> {
    pub l: u24,
    pub data: &'a [u8],
}
pub type Opaque0FfffffInner<'a> = (u24, &'a [u8]);
impl View for Opaque0Ffffff<'_> {
    type V = SpecOpaque0Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl<'a> From<Opaque0Ffffff<'a>> for Opaque0FfffffInner<'a> {
    fn ex_from(m: Opaque0Ffffff<'a>) -> Opaque0FfffffInner<'a> {
        (m.l, m.data)
    }
}
impl<'a> From<Opaque0FfffffInner<'a>> for Opaque0Ffffff<'a> {
    fn ex_from(m: Opaque0FfffffInner<'a>) -> Opaque0Ffffff<'a> {
        let (l, data) = m;
        Opaque0Ffffff {
            l,
            data,
        }
    }
}
pub struct Opaque0FfffffMapper;
impl View for Opaque0FfffffMapper {
    type V = Self;
    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl SpecIso for Opaque0FfffffMapper {
    type Src = SpecOpaque0FfffffInner;
    type Dst = SpecOpaque0Ffffff;
    proof fn spec_iso(s: Self::Src) {
    }
    proof fn spec_iso_rev(s: Self::Dst) {
    }
}
impl Iso for Opaque0FfffffMapper {
    type Src<'a> = Opaque0FfffffInner<'a>;
    type Dst<'a> = Opaque0Ffffff<'a>;
    type SrcOwned = Opaque0FfffffOwnedInner;
    type DstOwned = Opaque0FfffffOwned;
}
pub struct Opaque0FfffffOwned {
    pub l: u24,
    pub data: Vec<u8>,
}
pub type Opaque0FfffffOwnedInner = (u24, Vec<u8>);
impl View for Opaque0FfffffOwned {
    type V = SpecOpaque0Ffffff;
    open spec fn view(&self) -> Self::V {
        SpecOpaque0Ffffff {
            l: self.l@,
            data: self.data@,
        }
    }
}
impl From<Opaque0FfffffOwned> for Opaque0FfffffOwnedInner {
    fn ex_from(m: Opaque0FfffffOwned) -> Opaque0FfffffOwnedInner {
        (m.l, m.data)
    }
}
impl From<Opaque0FfffffOwnedInner> for Opaque0FfffffOwned {
    fn ex_from(m: Opaque0FfffffOwnedInner) -> Opaque0FfffffOwned {
        let (l, data) = m;
        Opaque0FfffffOwned {
            l,
            data,
        }
    }
}


pub struct SpecExtensionTypeCombinator(SpecExtensionTypeCombinatorAlias);

impl SpecCombinator for SpecExtensionTypeCombinator {
    type SpecResult = SpecExtensionType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecExtensionTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecExtensionTypeCombinatorAlias = U16Be;

pub struct ExtensionTypeCombinator(ExtensionTypeCombinatorAlias);

impl View for ExtensionTypeCombinator {
    type V = SpecExtensionTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionTypeCombinator(self.0@) }
}
impl Combinator for ExtensionTypeCombinator {
    type Result<'a> = ExtensionType;
    type Owned = ExtensionTypeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ExtensionTypeCombinatorAlias = U16Be;


pub struct SpecUint0FfffCombinator(SpecUint0FfffCombinatorAlias);

impl SpecCombinator for SpecUint0FfffCombinator {
    type SpecResult = SpecUint0Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FfffCombinatorAlias = U16Be;

pub struct Uint0FfffCombinator(Uint0FfffCombinatorAlias);

impl View for Uint0FfffCombinator {
    type V = SpecUint0FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FfffCombinator(self.0@) }
}
impl Combinator for Uint0FfffCombinator {
    type Result<'a> = Uint0Ffff;
    type Owned = Uint0FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint0FfffCombinatorAlias = U16Be;


pub struct SpecOpaque0FfffCombinator(SpecOpaque0FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffCombinator {
    type SpecResult = SpecOpaque0Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfffCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, Bytes>, Opaque0FfffMapper>;
pub struct Opaque0FfffCont;
pub struct Opaque0FfffCombinator(Opaque0FfffCombinatorAlias);

impl View for Opaque0FfffCombinator {
    type V = SpecOpaque0FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffCombinator(self.0@) }
}
impl Combinator for Opaque0FfffCombinator {
    type Result<'a> = Opaque0Ffff<'a>;
    type Owned = Opaque0FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque0FfffCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, Bytes, Opaque0FfffCont>, Opaque0FfffMapper>;


pub struct SpecExtensionCombinator(SpecExtensionCombinatorAlias);

impl SpecCombinator for SpecExtensionCombinator {
    type SpecResult = SpecExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecExtensionCombinatorAlias = Mapped<(SpecExtensionTypeCombinator, SpecOpaque0FfffCombinator), ExtensionMapper>;

pub struct ExtensionCombinator(ExtensionCombinatorAlias);

impl View for ExtensionCombinator {
    type V = SpecExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecExtensionCombinator(self.0@) }
}
impl Combinator for ExtensionCombinator {
    type Result<'a> = Extension<'a>;
    type Owned = ExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ExtensionCombinatorAlias = Mapped<(ExtensionTypeCombinator, Opaque0FfffCombinator), ExtensionMapper>;


pub struct SpecNewSessionTicketExtensionsExtensionsCombinator(SpecNewSessionTicketExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionsExtensionsCombinator {
    type SpecResult = SpecNewSessionTicketExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

pub struct NewSessionTicketExtensionsExtensionsCombinator(NewSessionTicketExtensionsExtensionsCombinatorAlias);

impl View for NewSessionTicketExtensionsExtensionsCombinator {
    type V = SpecNewSessionTicketExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionsExtensionsCombinator(self.0@) }
}
impl Combinator for NewSessionTicketExtensionsExtensionsCombinator {
    type Result<'a> = NewSessionTicketExtensionsExtensions<'a>;
    type Owned = NewSessionTicketExtensionsExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NewSessionTicketExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<ExtensionCombinator>>;


pub struct SpecProtocolVersionCombinator(SpecProtocolVersionCombinatorAlias);

impl SpecCombinator for SpecProtocolVersionCombinator {
    type SpecResult = SpecProtocolVersion;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolVersionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolVersionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolVersionCombinatorAlias = U16Be;

pub struct ProtocolVersionCombinator(ProtocolVersionCombinatorAlias);

impl View for ProtocolVersionCombinator {
    type V = SpecProtocolVersionCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolVersionCombinator(self.0@) }
}
impl Combinator for ProtocolVersionCombinator {
    type Result<'a> = ProtocolVersion;
    type Owned = ProtocolVersionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ProtocolVersionCombinatorAlias = U16Be;


pub struct SpecSupportedVersionsClientVersionsCombinator(SpecSupportedVersionsClientVersionsCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsClientVersionsCombinator {
    type SpecResult = SpecSupportedVersionsClientVersions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsClientVersionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsClientVersionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsClientVersionsCombinatorAlias = AndThen<Bytes, Repeat<SpecProtocolVersionCombinator>>;

pub struct SupportedVersionsClientVersionsCombinator(SupportedVersionsClientVersionsCombinatorAlias);

impl View for SupportedVersionsClientVersionsCombinator {
    type V = SpecSupportedVersionsClientVersionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsClientVersionsCombinator(self.0@) }
}
impl Combinator for SupportedVersionsClientVersionsCombinator {
    type Result<'a> = SupportedVersionsClientVersions;
    type Owned = SupportedVersionsClientVersionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SupportedVersionsClientVersionsCombinatorAlias = AndThen<Bytes, Repeat<ProtocolVersionCombinator>>;


pub struct SpecEcPointFormatCombinator(SpecEcPointFormatCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatCombinator {
    type SpecResult = SpecEcPointFormat;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatCombinatorAlias = U8;

pub struct EcPointFormatCombinator(EcPointFormatCombinatorAlias);

impl View for EcPointFormatCombinator {
    type V = SpecEcPointFormatCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatCombinator(self.0@) }
}
impl Combinator for EcPointFormatCombinator {
    type Result<'a> = EcPointFormat;
    type Owned = EcPointFormatOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EcPointFormatCombinatorAlias = U8;


pub struct SpecEcPointFormatListListCombinator(SpecEcPointFormatListListCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatListListCombinator {
    type SpecResult = SpecEcPointFormatListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatListListCombinatorAlias = AndThen<Bytes, Repeat<SpecEcPointFormatCombinator>>;

pub struct EcPointFormatListListCombinator(EcPointFormatListListCombinatorAlias);

impl View for EcPointFormatListListCombinator {
    type V = SpecEcPointFormatListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatListListCombinator(self.0@) }
}
impl Combinator for EcPointFormatListListCombinator {
    type Result<'a> = EcPointFormatListList;
    type Owned = EcPointFormatListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EcPointFormatListListCombinatorAlias = AndThen<Bytes, Repeat<EcPointFormatCombinator>>;

pub const ZEROBYTE_ZERO: u8 = 0;

pub struct SpecZeroByteCombinator(SpecZeroByteCombinatorAlias);

impl SpecCombinator for SpecZeroByteCombinator {
    type SpecResult = SpecZeroByte;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecZeroByteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecZeroByteCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;

pub struct ZeroByteCombinator(ZeroByteCombinatorAlias);

impl View for ZeroByteCombinator {
    type V = SpecZeroByteCombinator;
    closed spec fn view(&self) -> Self::V { SpecZeroByteCombinator(self.0@) }
}
impl Combinator for ZeroByteCombinator {
    type Result<'a> = ZeroByte;
    type Owned = ZeroByteOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ZeroByteCombinatorAlias = Mapped<Refined<U8, TagPred<u8>>, ZeroByteMapper>;


pub struct SpecPaddingExtensionPaddingCombinator(SpecPaddingExtensionPaddingCombinatorAlias);

impl SpecCombinator for SpecPaddingExtensionPaddingCombinator {
    type SpecResult = SpecPaddingExtensionPadding;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPaddingExtensionPaddingCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPaddingExtensionPaddingCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPaddingExtensionPaddingCombinatorAlias = AndThen<Bytes, Repeat<SpecZeroByteCombinator>>;

pub struct PaddingExtensionPaddingCombinator(PaddingExtensionPaddingCombinatorAlias);

impl View for PaddingExtensionPaddingCombinator {
    type V = SpecPaddingExtensionPaddingCombinator;
    closed spec fn view(&self) -> Self::V { SpecPaddingExtensionPaddingCombinator(self.0@) }
}
impl Combinator for PaddingExtensionPaddingCombinator {
    type Result<'a> = PaddingExtensionPadding;
    type Owned = PaddingExtensionPaddingOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PaddingExtensionPaddingCombinatorAlias = AndThen<Bytes, Repeat<ZeroByteCombinator>>;


pub struct SpecPskKeyExchangeModeCombinator(SpecPskKeyExchangeModeCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModeCombinator {
    type SpecResult = SpecPskKeyExchangeMode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModeCombinatorAlias = U8;

pub struct PskKeyExchangeModeCombinator(PskKeyExchangeModeCombinatorAlias);

impl View for PskKeyExchangeModeCombinator {
    type V = SpecPskKeyExchangeModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModeCombinator(self.0@) }
}
impl Combinator for PskKeyExchangeModeCombinator {
    type Result<'a> = PskKeyExchangeMode;
    type Owned = PskKeyExchangeModeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskKeyExchangeModeCombinatorAlias = U8;


pub struct SpecPskKeyExchangeModesModesCombinator(SpecPskKeyExchangeModesModesCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModesModesCombinator {
    type SpecResult = SpecPskKeyExchangeModesModes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModesModesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModesModesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModesModesCombinatorAlias = AndThen<Bytes, Repeat<SpecPskKeyExchangeModeCombinator>>;

pub struct PskKeyExchangeModesModesCombinator(PskKeyExchangeModesModesCombinatorAlias);

impl View for PskKeyExchangeModesModesCombinator {
    type V = SpecPskKeyExchangeModesModesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModesModesCombinator(self.0@) }
}
impl Combinator for PskKeyExchangeModesModesCombinator {
    type Result<'a> = PskKeyExchangeModesModes;
    type Owned = PskKeyExchangeModesModesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskKeyExchangeModesModesCombinatorAlias = AndThen<Bytes, Repeat<PskKeyExchangeModeCombinator>>;

impl SpecPred for Predicate11955646336730306823 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecUint1FfffCombinator(SpecUint1FfffCombinatorAlias);

impl SpecCombinator for SpecUint1FfffCombinator {
    type SpecResult = SpecUint1Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint1FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint1FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint1FfffCombinatorAlias = Refined<U16Be, Predicate11955646336730306823>;
pub struct Predicate11955646336730306823;
impl View for Predicate11955646336730306823 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate11955646336730306823 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct Uint1FfffCombinator(Uint1FfffCombinatorAlias);

impl View for Uint1FfffCombinator {
    type V = SpecUint1FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint1FfffCombinator(self.0@) }
}
impl Combinator for Uint1FfffCombinator {
    type Result<'a> = Uint1Ffff;
    type Owned = Uint1FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint1FfffCombinatorAlias = Refined<U16Be, Predicate11955646336730306823>;


pub struct SpecNameTypeCombinator(SpecNameTypeCombinatorAlias);

impl SpecCombinator for SpecNameTypeCombinator {
    type SpecResult = SpecNameType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNameTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNameTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNameTypeCombinatorAlias = U8;

pub struct NameTypeCombinator(NameTypeCombinatorAlias);

impl View for NameTypeCombinator {
    type V = SpecNameTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecNameTypeCombinator(self.0@) }
}
impl Combinator for NameTypeCombinator {
    type Result<'a> = NameType;
    type Owned = NameTypeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NameTypeCombinatorAlias = U8;


pub struct SpecOpaque1FfffCombinator(SpecOpaque1FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffCombinator {
    type SpecResult = SpecOpaque1Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfffCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, Bytes>, Opaque1FfffMapper>;
pub struct Opaque1FfffCont;
pub struct Opaque1FfffCombinator(Opaque1FfffCombinatorAlias);

impl View for Opaque1FfffCombinator {
    type V = SpecOpaque1FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffCombinator(self.0@) }
}
impl Combinator for Opaque1FfffCombinator {
    type Result<'a> = Opaque1Ffff<'a>;
    type Owned = Opaque1FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque1FfffCombinatorAlias = Mapped<Depend<Uint1FfffCombinator, Bytes, Opaque1FfffCont>, Opaque1FfffMapper>;


pub struct SpecHostNameCombinator(SpecHostNameCombinatorAlias);

impl SpecCombinator for SpecHostNameCombinator {
    type SpecResult = SpecHostName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHostNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHostNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHostNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct HostNameCombinator(HostNameCombinatorAlias);

impl View for HostNameCombinator {
    type V = SpecHostNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecHostNameCombinator(self.0@) }
}
impl Combinator for HostNameCombinator {
    type Result<'a> = HostName<'a>;
    type Owned = HostNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HostNameCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecUnknownNameCombinator(SpecUnknownNameCombinatorAlias);

impl SpecCombinator for SpecUnknownNameCombinator {
    type SpecResult = SpecUnknownName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUnknownNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUnknownNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct UnknownNameCombinator(UnknownNameCombinatorAlias);

impl View for UnknownNameCombinator {
    type V = SpecUnknownNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownNameCombinator(self.0@) }
}
impl Combinator for UnknownNameCombinator {
    type Result<'a> = UnknownName<'a>;
    type Owned = UnknownNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UnknownNameCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecServerNameNameCombinator(SpecServerNameNameCombinatorAlias);

impl SpecCombinator for SpecServerNameNameCombinator {
    type SpecResult = SpecServerNameName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameNameCombinatorAlias = Mapped<OrdChoice<Cond<SpecHostNameCombinator>, Cond<SpecUnknownNameCombinator>>, ServerNameNameMapper>;

pub struct ServerNameNameCombinator(ServerNameNameCombinatorAlias);

impl View for ServerNameNameCombinator {
    type V = SpecServerNameNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameNameCombinator(self.0@) }
}
impl Combinator for ServerNameNameCombinator {
    type Result<'a> = ServerNameName<'a>;
    type Owned = ServerNameNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerNameNameCombinatorAlias = Mapped<OrdChoice<Cond<HostNameCombinator>, Cond<UnknownNameCombinator>>, ServerNameNameMapper>;


pub struct SpecServerNameCombinator(SpecServerNameCombinatorAlias);

impl SpecCombinator for SpecServerNameCombinator {
    type SpecResult = SpecServerName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameCombinatorAlias = Mapped<SpecDepend<SpecNameTypeCombinator, SpecServerNameNameCombinator>, ServerNameMapper>;
pub struct ServerNameCont;
pub struct ServerNameCombinator(ServerNameCombinatorAlias);

impl View for ServerNameCombinator {
    type V = SpecServerNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameCombinator(self.0@) }
}
impl Combinator for ServerNameCombinator {
    type Result<'a> = ServerName<'a>;
    type Owned = ServerNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerNameCombinatorAlias = Mapped<Depend<NameTypeCombinator, ServerNameNameCombinator, ServerNameCont>, ServerNameMapper>;


pub struct SpecServerNameListListCombinator(SpecServerNameListListCombinatorAlias);

impl SpecCombinator for SpecServerNameListListCombinator {
    type SpecResult = SpecServerNameListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameListListCombinatorAlias = AndThen<Bytes, Repeat<SpecServerNameCombinator>>;

pub struct ServerNameListListCombinator(ServerNameListListCombinatorAlias);

impl View for ServerNameListListCombinator {
    type V = SpecServerNameListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameListListCombinator(self.0@) }
}
impl Combinator for ServerNameListListCombinator {
    type Result<'a> = ServerNameListList<'a>;
    type Owned = ServerNameListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerNameListListCombinatorAlias = AndThen<Bytes, Repeat<ServerNameCombinator>>;


pub struct SpecServerNameListCombinator(SpecServerNameListCombinatorAlias);

impl SpecCombinator for SpecServerNameListCombinator {
    type SpecResult = SpecServerNameList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerNameListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerNameListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, SpecServerNameListListCombinator>, ServerNameListMapper>;
pub struct ServerNameListCont;
pub struct ServerNameListCombinator(ServerNameListCombinatorAlias);

impl View for ServerNameListCombinator {
    type V = SpecServerNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerNameListCombinator(self.0@) }
}
impl Combinator for ServerNameListCombinator {
    type Result<'a> = ServerNameList<'a>;
    type Owned = ServerNameListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerNameListCombinatorAlias = Mapped<Depend<Uint1FfffCombinator, ServerNameListListCombinator, ServerNameListCont>, ServerNameListMapper>;


pub struct SpecMaxFragmentLengthCombinator(SpecMaxFragmentLengthCombinatorAlias);

impl SpecCombinator for SpecMaxFragmentLengthCombinator {
    type SpecResult = SpecMaxFragmentLength;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMaxFragmentLengthCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMaxFragmentLengthCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMaxFragmentLengthCombinatorAlias = U8;

pub struct MaxFragmentLengthCombinator(MaxFragmentLengthCombinatorAlias);

impl View for MaxFragmentLengthCombinator {
    type V = SpecMaxFragmentLengthCombinator;
    closed spec fn view(&self) -> Self::V { SpecMaxFragmentLengthCombinator(self.0@) }
}
impl Combinator for MaxFragmentLengthCombinator {
    type Result<'a> = MaxFragmentLength;
    type Owned = MaxFragmentLengthOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type MaxFragmentLengthCombinatorAlias = U8;


pub struct SpecResponderIdCombinator(SpecResponderIdCombinatorAlias);

impl SpecCombinator for SpecResponderIdCombinator {
    type SpecResult = SpecResponderId;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct ResponderIdCombinator(ResponderIdCombinatorAlias);

impl View for ResponderIdCombinator {
    type V = SpecResponderIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdCombinator(self.0@) }
}
impl Combinator for ResponderIdCombinator {
    type Result<'a> = ResponderId<'a>;
    type Owned = ResponderIdOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ResponderIdCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecResponderIdListListCombinator(SpecResponderIdListListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListListCombinator {
    type SpecResult = SpecResponderIdListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdListListCombinatorAlias = AndThen<Bytes, Repeat<SpecResponderIdCombinator>>;

pub struct ResponderIdListListCombinator(ResponderIdListListCombinatorAlias);

impl View for ResponderIdListListCombinator {
    type V = SpecResponderIdListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListListCombinator(self.0@) }
}
impl Combinator for ResponderIdListListCombinator {
    type Result<'a> = ResponderIdListList<'a>;
    type Owned = ResponderIdListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ResponderIdListListCombinatorAlias = AndThen<Bytes, Repeat<ResponderIdCombinator>>;


pub struct SpecResponderIdListCombinator(SpecResponderIdListCombinatorAlias);

impl SpecCombinator for SpecResponderIdListCombinator {
    type SpecResult = SpecResponderIdList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecResponderIdListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecResponderIdListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecResponderIdListCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecResponderIdListListCombinator>, ResponderIdListMapper>;
pub struct ResponderIdListCont;
pub struct ResponderIdListCombinator(ResponderIdListCombinatorAlias);

impl View for ResponderIdListCombinator {
    type V = SpecResponderIdListCombinator;
    closed spec fn view(&self) -> Self::V { SpecResponderIdListCombinator(self.0@) }
}
impl Combinator for ResponderIdListCombinator {
    type Result<'a> = ResponderIdList<'a>;
    type Owned = ResponderIdListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ResponderIdListCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, ResponderIdListListCombinator, ResponderIdListCont>, ResponderIdListMapper>;


pub struct SpecOcspExtensionsCombinator(SpecOcspExtensionsCombinatorAlias);

impl SpecCombinator for SpecOcspExtensionsCombinator {
    type SpecResult = SpecOcspExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOcspExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOcspExtensionsCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct OcspExtensionsCombinator(OcspExtensionsCombinatorAlias);

impl View for OcspExtensionsCombinator {
    type V = SpecOcspExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspExtensionsCombinator(self.0@) }
}
impl Combinator for OcspExtensionsCombinator {
    type Result<'a> = OcspExtensions<'a>;
    type Owned = OcspExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OcspExtensionsCombinatorAlias = Opaque0FfffCombinator;


pub struct SpecOscpStatusRequestCombinator(SpecOscpStatusRequestCombinatorAlias);

impl SpecCombinator for SpecOscpStatusRequestCombinator {
    type SpecResult = SpecOscpStatusRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOscpStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOscpStatusRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOscpStatusRequestCombinatorAlias = Mapped<(SpecResponderIdListCombinator, SpecOcspExtensionsCombinator), OscpStatusRequestMapper>;

pub struct OscpStatusRequestCombinator(OscpStatusRequestCombinatorAlias);

impl View for OscpStatusRequestCombinator {
    type V = SpecOscpStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecOscpStatusRequestCombinator(self.0@) }
}
impl Combinator for OscpStatusRequestCombinator {
    type Result<'a> = OscpStatusRequest<'a>;
    type Owned = OscpStatusRequestOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OscpStatusRequestCombinatorAlias = Mapped<(ResponderIdListCombinator, OcspExtensionsCombinator), OscpStatusRequestMapper>;

pub const CERTIFICATESTATUSREQUEST_STATUS_TYPE: u8 = 1;

pub struct SpecCertificateStatusRequestCombinator(SpecCertificateStatusRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusRequestCombinator {
    type SpecResult = SpecCertificateStatusRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateStatusRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateStatusRequestCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, SpecOscpStatusRequestCombinator), CertificateStatusRequestMapper>;

pub struct CertificateStatusRequestCombinator(CertificateStatusRequestCombinatorAlias);

impl View for CertificateStatusRequestCombinator {
    type V = SpecCertificateStatusRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusRequestCombinator(self.0@) }
}
impl Combinator for CertificateStatusRequestCombinator {
    type Result<'a> = CertificateStatusRequest<'a>;
    type Owned = CertificateStatusRequestOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateStatusRequestCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, OscpStatusRequestCombinator), CertificateStatusRequestMapper>;

impl SpecPred for Predicate5950696943328973166 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecUint2FfffCombinator(SpecUint2FfffCombinatorAlias);

impl SpecCombinator for SpecUint2FfffCombinator {
    type SpecResult = SpecUint2Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint2FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint2FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint2FfffCombinatorAlias = Refined<U16Be, Predicate5950696943328973166>;
pub struct Predicate5950696943328973166;
impl View for Predicate5950696943328973166 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate5950696943328973166 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct Uint2FfffCombinator(Uint2FfffCombinatorAlias);

impl View for Uint2FfffCombinator {
    type V = SpecUint2FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint2FfffCombinator(self.0@) }
}
impl Combinator for Uint2FfffCombinator {
    type Result<'a> = Uint2Ffff;
    type Owned = Uint2FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint2FfffCombinatorAlias = Refined<U16Be, Predicate5950696943328973166>;


pub struct SpecNamedGroupCombinator(SpecNamedGroupCombinatorAlias);

impl SpecCombinator for SpecNamedGroupCombinator {
    type SpecResult = SpecNamedGroup;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupCombinatorAlias = U16Be;

pub struct NamedGroupCombinator(NamedGroupCombinatorAlias);

impl View for NamedGroupCombinator {
    type V = SpecNamedGroupCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupCombinator(self.0@) }
}
impl Combinator for NamedGroupCombinator {
    type Result<'a> = NamedGroup;
    type Owned = NamedGroupOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NamedGroupCombinatorAlias = U16Be;


pub struct SpecNamedGroupListListCombinator(SpecNamedGroupListListCombinatorAlias);

impl SpecCombinator for SpecNamedGroupListListCombinator {
    type SpecResult = SpecNamedGroupListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupListListCombinatorAlias = AndThen<Bytes, Repeat<SpecNamedGroupCombinator>>;

pub struct NamedGroupListListCombinator(NamedGroupListListCombinatorAlias);

impl View for NamedGroupListListCombinator {
    type V = SpecNamedGroupListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupListListCombinator(self.0@) }
}
impl Combinator for NamedGroupListListCombinator {
    type Result<'a> = NamedGroupListList;
    type Owned = NamedGroupListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NamedGroupListListCombinatorAlias = AndThen<Bytes, Repeat<NamedGroupCombinator>>;


pub struct SpecNamedGroupListCombinator(SpecNamedGroupListCombinatorAlias);

impl SpecCombinator for SpecNamedGroupListCombinator {
    type SpecResult = SpecNamedGroupList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNamedGroupListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNamedGroupListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNamedGroupListCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecNamedGroupListListCombinator>, NamedGroupListMapper>;
pub struct NamedGroupListCont;
pub struct NamedGroupListCombinator(NamedGroupListCombinatorAlias);

impl View for NamedGroupListCombinator {
    type V = SpecNamedGroupListCombinator;
    closed spec fn view(&self) -> Self::V { SpecNamedGroupListCombinator(self.0@) }
}
impl Combinator for NamedGroupListCombinator {
    type Result<'a> = NamedGroupList;
    type Owned = NamedGroupListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NamedGroupListCombinatorAlias = Mapped<Depend<Uint2FfffCombinator, NamedGroupListListCombinator, NamedGroupListCont>, NamedGroupListMapper>;

impl SpecPred for Predicate13930216038658429813 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 255) {
            true
        } else {
            false
        }
    }
}

pub struct SpecUint1FfCombinator(SpecUint1FfCombinatorAlias);

impl SpecCombinator for SpecUint1FfCombinator {
    type SpecResult = SpecUint1Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint1FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint1FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint1FfCombinatorAlias = Refined<U8, Predicate13930216038658429813>;
pub struct Predicate13930216038658429813;
impl View for Predicate13930216038658429813 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate13930216038658429813 {
    type Input<'a> = u8;
    type InputOwned = u8;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 1 && i <= 255) {
            true
        } else {
            false
        }
    }
}

pub struct Uint1FfCombinator(Uint1FfCombinatorAlias);

impl View for Uint1FfCombinator {
    type V = SpecUint1FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint1FfCombinator(self.0@) }
}
impl Combinator for Uint1FfCombinator {
    type Result<'a> = Uint1Ff;
    type Owned = Uint1FfOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint1FfCombinatorAlias = Refined<U8, Predicate13930216038658429813>;


pub struct SpecEcPointFormatListCombinator(SpecEcPointFormatListCombinatorAlias);

impl SpecCombinator for SpecEcPointFormatListCombinator {
    type SpecResult = SpecEcPointFormatList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEcPointFormatListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEcPointFormatListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEcPointFormatListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecEcPointFormatListListCombinator>, EcPointFormatListMapper>;
pub struct EcPointFormatListCont;
pub struct EcPointFormatListCombinator(EcPointFormatListCombinatorAlias);

impl View for EcPointFormatListCombinator {
    type V = SpecEcPointFormatListCombinator;
    closed spec fn view(&self) -> Self::V { SpecEcPointFormatListCombinator(self.0@) }
}
impl Combinator for EcPointFormatListCombinator {
    type Result<'a> = EcPointFormatList;
    type Owned = EcPointFormatListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EcPointFormatListCombinatorAlias = Mapped<Depend<Uint1FfCombinator, EcPointFormatListListCombinator, EcPointFormatListCont>, EcPointFormatListMapper>;

impl SpecPred for Predicate13238841935489611399 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

pub struct SpecUint2FffeCombinator(SpecUint2FffeCombinatorAlias);

impl SpecCombinator for SpecUint2FffeCombinator {
    type SpecResult = SpecUint2Fffe;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint2FffeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint2FffeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint2FffeCombinatorAlias = Refined<U16Be, Predicate13238841935489611399>;
pub struct Predicate13238841935489611399;
impl View for Predicate13238841935489611399 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate13238841935489611399 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

pub struct Uint2FffeCombinator(Uint2FffeCombinatorAlias);

impl View for Uint2FffeCombinator {
    type V = SpecUint2FffeCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint2FffeCombinator(self.0@) }
}
impl Combinator for Uint2FffeCombinator {
    type Result<'a> = Uint2Fffe;
    type Owned = Uint2FffeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint2FffeCombinatorAlias = Refined<U16Be, Predicate13238841935489611399>;


pub struct SpecSignatureSchemeCombinator(SpecSignatureSchemeCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeCombinator {
    type SpecResult = SpecSignatureScheme;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeCombinatorAlias = U16Be;

pub struct SignatureSchemeCombinator(SignatureSchemeCombinatorAlias);

impl View for SignatureSchemeCombinator {
    type V = SpecSignatureSchemeCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeCombinator(self.0@) }
}
impl Combinator for SignatureSchemeCombinator {
    type Result<'a> = SignatureScheme;
    type Owned = SignatureSchemeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SignatureSchemeCombinatorAlias = U16Be;


pub struct SpecSignatureSchemeListListCombinator(SpecSignatureSchemeListListCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeListListCombinator {
    type SpecResult = SpecSignatureSchemeListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeListListCombinatorAlias = AndThen<Bytes, Repeat<SpecSignatureSchemeCombinator>>;

pub struct SignatureSchemeListListCombinator(SignatureSchemeListListCombinatorAlias);

impl View for SignatureSchemeListListCombinator {
    type V = SpecSignatureSchemeListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeListListCombinator(self.0@) }
}
impl Combinator for SignatureSchemeListListCombinator {
    type Result<'a> = SignatureSchemeListList;
    type Owned = SignatureSchemeListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SignatureSchemeListListCombinatorAlias = AndThen<Bytes, Repeat<SignatureSchemeCombinator>>;


pub struct SpecSignatureSchemeListCombinator(SpecSignatureSchemeListCombinatorAlias);

impl SpecCombinator for SpecSignatureSchemeListCombinator {
    type SpecResult = SpecSignatureSchemeList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignatureSchemeListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignatureSchemeListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignatureSchemeListCombinatorAlias = Mapped<SpecDepend<SpecUint2FffeCombinator, SpecSignatureSchemeListListCombinator>, SignatureSchemeListMapper>;
pub struct SignatureSchemeListCont;
pub struct SignatureSchemeListCombinator(SignatureSchemeListCombinatorAlias);

impl View for SignatureSchemeListCombinator {
    type V = SpecSignatureSchemeListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignatureSchemeListCombinator(self.0@) }
}
impl Combinator for SignatureSchemeListCombinator {
    type Result<'a> = SignatureSchemeList;
    type Owned = SignatureSchemeListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SignatureSchemeListCombinatorAlias = Mapped<Depend<Uint2FffeCombinator, SignatureSchemeListListCombinator, SignatureSchemeListCont>, SignatureSchemeListMapper>;


pub struct SpecSrtpProtectionProfileCombinator(SpecSrtpProtectionProfileCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfileCombinator {
    type SpecResult = SpecSrtpProtectionProfile;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfileCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfileCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfileCombinatorAlias = BytesN<2>;

pub struct SrtpProtectionProfileCombinator(SrtpProtectionProfileCombinatorAlias);

impl View for SrtpProtectionProfileCombinator {
    type V = SpecSrtpProtectionProfileCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfileCombinator(self.0@) }
}
impl Combinator for SrtpProtectionProfileCombinator {
    type Result<'a> = SrtpProtectionProfile<'a>;
    type Owned = SrtpProtectionProfileOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SrtpProtectionProfileCombinatorAlias = BytesN<2>;


pub struct SpecSrtpProtectionProfilesListCombinator(SpecSrtpProtectionProfilesListCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfilesListCombinator {
    type SpecResult = SpecSrtpProtectionProfilesList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfilesListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfilesListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfilesListCombinatorAlias = AndThen<Bytes, Repeat<SpecSrtpProtectionProfileCombinator>>;

pub struct SrtpProtectionProfilesListCombinator(SrtpProtectionProfilesListCombinatorAlias);

impl View for SrtpProtectionProfilesListCombinator {
    type V = SpecSrtpProtectionProfilesListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfilesListCombinator(self.0@) }
}
impl Combinator for SrtpProtectionProfilesListCombinator {
    type Result<'a> = SrtpProtectionProfilesList<'a>;
    type Owned = SrtpProtectionProfilesListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SrtpProtectionProfilesListCombinatorAlias = AndThen<Bytes, Repeat<SrtpProtectionProfileCombinator>>;


pub struct SpecSrtpProtectionProfilesCombinator(SpecSrtpProtectionProfilesCombinatorAlias);

impl SpecCombinator for SpecSrtpProtectionProfilesCombinator {
    type SpecResult = SpecSrtpProtectionProfiles;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSrtpProtectionProfilesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSrtpProtectionProfilesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSrtpProtectionProfilesCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecSrtpProtectionProfilesListCombinator>, SrtpProtectionProfilesMapper>;
pub struct SrtpProtectionProfilesCont;
pub struct SrtpProtectionProfilesCombinator(SrtpProtectionProfilesCombinatorAlias);

impl View for SrtpProtectionProfilesCombinator {
    type V = SpecSrtpProtectionProfilesCombinator;
    closed spec fn view(&self) -> Self::V { SpecSrtpProtectionProfilesCombinator(self.0@) }
}
impl Combinator for SrtpProtectionProfilesCombinator {
    type Result<'a> = SrtpProtectionProfiles<'a>;
    type Owned = SrtpProtectionProfilesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SrtpProtectionProfilesCombinatorAlias = Mapped<Depend<Uint2FfffCombinator, SrtpProtectionProfilesListCombinator, SrtpProtectionProfilesCont>, SrtpProtectionProfilesMapper>;


pub struct SpecUint0FfCombinator(SpecUint0FfCombinatorAlias);

impl SpecCombinator for SpecUint0FfCombinator {
    type SpecResult = SpecUint0Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FfCombinatorAlias = U8;

pub struct Uint0FfCombinator(Uint0FfCombinatorAlias);

impl View for Uint0FfCombinator {
    type V = SpecUint0FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FfCombinator(self.0@) }
}
impl Combinator for Uint0FfCombinator {
    type Result<'a> = Uint0Ff;
    type Owned = Uint0FfOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint0FfCombinatorAlias = U8;


pub struct SpecOpaque0FfCombinator(SpecOpaque0FfCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfCombinator {
    type SpecResult = SpecOpaque0Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfCombinatorAlias = Mapped<SpecDepend<SpecUint0FfCombinator, Bytes>, Opaque0FfMapper>;
pub struct Opaque0FfCont;
pub struct Opaque0FfCombinator(Opaque0FfCombinatorAlias);

impl View for Opaque0FfCombinator {
    type V = SpecOpaque0FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfCombinator(self.0@) }
}
impl Combinator for Opaque0FfCombinator {
    type Result<'a> = Opaque0Ff<'a>;
    type Owned = Opaque0FfOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque0FfCombinatorAlias = Mapped<Depend<Uint0FfCombinator, Bytes, Opaque0FfCont>, Opaque0FfMapper>;


pub struct SpecUseSrtpDataCombinator(SpecUseSrtpDataCombinatorAlias);

impl SpecCombinator for SpecUseSrtpDataCombinator {
    type SpecResult = SpecUseSrtpData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUseSrtpDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUseSrtpDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUseSrtpDataCombinatorAlias = Mapped<(SpecSrtpProtectionProfilesCombinator, SpecOpaque0FfCombinator), UseSrtpDataMapper>;

pub struct UseSrtpDataCombinator(UseSrtpDataCombinatorAlias);

impl View for UseSrtpDataCombinator {
    type V = SpecUseSrtpDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecUseSrtpDataCombinator(self.0@) }
}
impl Combinator for UseSrtpDataCombinator {
    type Result<'a> = UseSrtpData<'a>;
    type Owned = UseSrtpDataOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UseSrtpDataCombinatorAlias = Mapped<(SrtpProtectionProfilesCombinator, Opaque0FfCombinator), UseSrtpDataMapper>;


pub struct SpecHeartbeatModeCombinator(SpecHeartbeatModeCombinatorAlias);

impl SpecCombinator for SpecHeartbeatModeCombinator {
    type SpecResult = SpecHeartbeatMode;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHeartbeatModeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatModeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHeartbeatModeCombinatorAlias = U8;

pub struct HeartbeatModeCombinator(HeartbeatModeCombinatorAlias);

impl View for HeartbeatModeCombinator {
    type V = SpecHeartbeatModeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatModeCombinator(self.0@) }
}
impl Combinator for HeartbeatModeCombinator {
    type Result<'a> = HeartbeatMode;
    type Owned = HeartbeatModeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HeartbeatModeCombinatorAlias = U8;


pub struct SpecOpaque1FfCombinator(SpecOpaque1FfCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfCombinator {
    type SpecResult = SpecOpaque1Ff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, Bytes>, Opaque1FfMapper>;
pub struct Opaque1FfCont;
pub struct Opaque1FfCombinator(Opaque1FfCombinatorAlias);

impl View for Opaque1FfCombinator {
    type V = SpecOpaque1FfCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfCombinator(self.0@) }
}
impl Combinator for Opaque1FfCombinator {
    type Result<'a> = Opaque1Ff<'a>;
    type Owned = Opaque1FfOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque1FfCombinatorAlias = Mapped<Depend<Uint1FfCombinator, Bytes, Opaque1FfCont>, Opaque1FfMapper>;


pub struct SpecProtocolNameCombinator(SpecProtocolNameCombinatorAlias);

impl SpecCombinator for SpecProtocolNameCombinator {
    type SpecResult = SpecProtocolName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameCombinatorAlias = SpecOpaque1FfCombinator;

pub struct ProtocolNameCombinator(ProtocolNameCombinatorAlias);

impl View for ProtocolNameCombinator {
    type V = SpecProtocolNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameCombinator(self.0@) }
}
impl Combinator for ProtocolNameCombinator {
    type Result<'a> = ProtocolName<'a>;
    type Owned = ProtocolNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ProtocolNameCombinatorAlias = Opaque1FfCombinator;


pub struct SpecProtocolNameListListCombinator(SpecProtocolNameListListCombinatorAlias);

impl SpecCombinator for SpecProtocolNameListListCombinator {
    type SpecResult = SpecProtocolNameListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameListListCombinatorAlias = AndThen<Bytes, Repeat<SpecProtocolNameCombinator>>;

pub struct ProtocolNameListListCombinator(ProtocolNameListListCombinatorAlias);

impl View for ProtocolNameListListCombinator {
    type V = SpecProtocolNameListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameListListCombinator(self.0@) }
}
impl Combinator for ProtocolNameListListCombinator {
    type Result<'a> = ProtocolNameListList<'a>;
    type Owned = ProtocolNameListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ProtocolNameListListCombinatorAlias = AndThen<Bytes, Repeat<ProtocolNameCombinator>>;


pub struct SpecProtocolNameListCombinator(SpecProtocolNameListCombinatorAlias);

impl SpecCombinator for SpecProtocolNameListCombinator {
    type SpecResult = SpecProtocolNameList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecProtocolNameListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecProtocolNameListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecProtocolNameListCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecProtocolNameListListCombinator>, ProtocolNameListMapper>;
pub struct ProtocolNameListCont;
pub struct ProtocolNameListCombinator(ProtocolNameListCombinatorAlias);

impl View for ProtocolNameListCombinator {
    type V = SpecProtocolNameListCombinator;
    closed spec fn view(&self) -> Self::V { SpecProtocolNameListCombinator(self.0@) }
}
impl Combinator for ProtocolNameListCombinator {
    type Result<'a> = ProtocolNameList<'a>;
    type Owned = ProtocolNameListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ProtocolNameListCombinatorAlias = Mapped<Depend<Uint2FfffCombinator, ProtocolNameListListCombinator, ProtocolNameListCont>, ProtocolNameListMapper>;


pub struct SpecSerializedSctCombinator(SpecSerializedSctCombinatorAlias);

impl SpecCombinator for SpecSerializedSctCombinator {
    type SpecResult = SpecSerializedSct;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSerializedSctCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSerializedSctCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSerializedSctCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct SerializedSctCombinator(SerializedSctCombinatorAlias);

impl View for SerializedSctCombinator {
    type V = SpecSerializedSctCombinator;
    closed spec fn view(&self) -> Self::V { SpecSerializedSctCombinator(self.0@) }
}
impl Combinator for SerializedSctCombinator {
    type Result<'a> = SerializedSct<'a>;
    type Owned = SerializedSctOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SerializedSctCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecSignedCertificateTimestampListListCombinator(SpecSignedCertificateTimestampListListCombinatorAlias);

impl SpecCombinator for SpecSignedCertificateTimestampListListCombinator {
    type SpecResult = SpecSignedCertificateTimestampListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignedCertificateTimestampListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignedCertificateTimestampListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignedCertificateTimestampListListCombinatorAlias = AndThen<Bytes, Repeat<SpecSerializedSctCombinator>>;

pub struct SignedCertificateTimestampListListCombinator(SignedCertificateTimestampListListCombinatorAlias);

impl View for SignedCertificateTimestampListListCombinator {
    type V = SpecSignedCertificateTimestampListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignedCertificateTimestampListListCombinator(self.0@) }
}
impl Combinator for SignedCertificateTimestampListListCombinator {
    type Result<'a> = SignedCertificateTimestampListList<'a>;
    type Owned = SignedCertificateTimestampListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SignedCertificateTimestampListListCombinatorAlias = AndThen<Bytes, Repeat<SerializedSctCombinator>>;


pub struct SpecSignedCertificateTimestampListCombinator(SpecSignedCertificateTimestampListCombinatorAlias);

impl SpecCombinator for SpecSignedCertificateTimestampListCombinator {
    type SpecResult = SpecSignedCertificateTimestampList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSignedCertificateTimestampListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSignedCertificateTimestampListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSignedCertificateTimestampListCombinatorAlias = Mapped<SpecDepend<SpecUint1FfffCombinator, SpecSignedCertificateTimestampListListCombinator>, SignedCertificateTimestampListMapper>;
pub struct SignedCertificateTimestampListCont;
pub struct SignedCertificateTimestampListCombinator(SignedCertificateTimestampListCombinatorAlias);

impl View for SignedCertificateTimestampListCombinator {
    type V = SpecSignedCertificateTimestampListCombinator;
    closed spec fn view(&self) -> Self::V { SpecSignedCertificateTimestampListCombinator(self.0@) }
}
impl Combinator for SignedCertificateTimestampListCombinator {
    type Result<'a> = SignedCertificateTimestampList<'a>;
    type Owned = SignedCertificateTimestampListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SignedCertificateTimestampListCombinatorAlias = Mapped<Depend<Uint1FfffCombinator, SignedCertificateTimestampListListCombinator, SignedCertificateTimestampListCont>, SignedCertificateTimestampListMapper>;


pub struct SpecCertificateTypeCombinator(SpecCertificateTypeCombinatorAlias);

impl SpecCombinator for SpecCertificateTypeCombinator {
    type SpecResult = SpecCertificateType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateTypeCombinatorAlias = U8;

pub struct CertificateTypeCombinator(CertificateTypeCombinatorAlias);

impl View for CertificateTypeCombinator {
    type V = SpecCertificateTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateTypeCombinator(self.0@) }
}
impl Combinator for CertificateTypeCombinator {
    type Result<'a> = CertificateType;
    type Owned = CertificateTypeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateTypeCombinatorAlias = U8;


pub struct SpecClientCertTypeClientExtensionTypesCombinator(SpecClientCertTypeClientExtensionTypesCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeClientExtensionTypesCombinator {
    type SpecResult = SpecClientCertTypeClientExtensionTypes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeClientExtensionTypesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeClientExtensionTypesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateTypeCombinator>>;

pub struct ClientCertTypeClientExtensionTypesCombinator(ClientCertTypeClientExtensionTypesCombinatorAlias);

impl View for ClientCertTypeClientExtensionTypesCombinator {
    type V = SpecClientCertTypeClientExtensionTypesCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeClientExtensionTypesCombinator(self.0@) }
}
impl Combinator for ClientCertTypeClientExtensionTypesCombinator {
    type Result<'a> = ClientCertTypeClientExtensionTypes;
    type Owned = ClientCertTypeClientExtensionTypesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<CertificateTypeCombinator>>;


pub struct SpecClientCertTypeClientExtensionCombinator(SpecClientCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    type SpecResult = SpecClientCertTypeClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeClientExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecClientCertTypeClientExtensionTypesCombinator>, ClientCertTypeClientExtensionMapper>;
pub struct ClientCertTypeClientExtensionCont;
pub struct ClientCertTypeClientExtensionCombinator(ClientCertTypeClientExtensionCombinatorAlias);

impl View for ClientCertTypeClientExtensionCombinator {
    type V = SpecClientCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeClientExtensionCombinator(self.0@) }
}
impl Combinator for ClientCertTypeClientExtensionCombinator {
    type Result<'a> = ClientCertTypeClientExtension;
    type Owned = ClientCertTypeClientExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientCertTypeClientExtensionCombinatorAlias = Mapped<Depend<Uint1FfCombinator, ClientCertTypeClientExtensionTypesCombinator, ClientCertTypeClientExtensionCont>, ClientCertTypeClientExtensionMapper>;


pub struct SpecServerCertTypeClientExtensionTypesCombinator(SpecServerCertTypeClientExtensionTypesCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeClientExtensionTypesCombinator {
    type SpecResult = SpecServerCertTypeClientExtensionTypes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeClientExtensionTypesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeClientExtensionTypesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateTypeCombinator>>;

pub struct ServerCertTypeClientExtensionTypesCombinator(ServerCertTypeClientExtensionTypesCombinatorAlias);

impl View for ServerCertTypeClientExtensionTypesCombinator {
    type V = SpecServerCertTypeClientExtensionTypesCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeClientExtensionTypesCombinator(self.0@) }
}
impl Combinator for ServerCertTypeClientExtensionTypesCombinator {
    type Result<'a> = ServerCertTypeClientExtensionTypes;
    type Owned = ServerCertTypeClientExtensionTypesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerCertTypeClientExtensionTypesCombinatorAlias = AndThen<Bytes, Repeat<CertificateTypeCombinator>>;


pub struct SpecServerCertTypeClientExtensionCombinator(SpecServerCertTypeClientExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    type SpecResult = SpecServerCertTypeClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeClientExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecServerCertTypeClientExtensionTypesCombinator>, ServerCertTypeClientExtensionMapper>;
pub struct ServerCertTypeClientExtensionCont;
pub struct ServerCertTypeClientExtensionCombinator(ServerCertTypeClientExtensionCombinatorAlias);

impl View for ServerCertTypeClientExtensionCombinator {
    type V = SpecServerCertTypeClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeClientExtensionCombinator(self.0@) }
}
impl Combinator for ServerCertTypeClientExtensionCombinator {
    type Result<'a> = ServerCertTypeClientExtension;
    type Owned = ServerCertTypeClientExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerCertTypeClientExtensionCombinatorAlias = Mapped<Depend<Uint1FfCombinator, ServerCertTypeClientExtensionTypesCombinator, ServerCertTypeClientExtensionCont>, ServerCertTypeClientExtensionMapper>;


pub struct SpecPaddingExtensionCombinator(SpecPaddingExtensionCombinatorAlias);

impl SpecCombinator for SpecPaddingExtensionCombinator {
    type SpecResult = SpecPaddingExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPaddingExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPaddingExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPaddingExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecPaddingExtensionPaddingCombinator>, PaddingExtensionMapper>;
pub struct PaddingExtensionCont;
pub struct PaddingExtensionCombinator(PaddingExtensionCombinatorAlias);

impl View for PaddingExtensionCombinator {
    type V = SpecPaddingExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPaddingExtensionCombinator(self.0@) }
}
impl Combinator for PaddingExtensionCombinator {
    type Result<'a> = PaddingExtension;
    type Owned = PaddingExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PaddingExtensionCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, PaddingExtensionPaddingCombinator, PaddingExtensionCont>, PaddingExtensionMapper>;


pub struct SpecEmptyCombinator(SpecEmptyCombinatorAlias);

impl SpecCombinator for SpecEmptyCombinator {
    type SpecResult = SpecEmpty;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEmptyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEmptyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEmptyCombinatorAlias = BytesN<0>;

pub struct EmptyCombinator(EmptyCombinatorAlias);

impl View for EmptyCombinator {
    type V = SpecEmptyCombinator;
    closed spec fn view(&self) -> Self::V { SpecEmptyCombinator(self.0@) }
}
impl Combinator for EmptyCombinator {
    type Result<'a> = Empty<'a>;
    type Owned = EmptyOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EmptyCombinatorAlias = BytesN<0>;


pub struct SpecPskIdentityCombinator(SpecPskIdentityCombinatorAlias);

impl SpecCombinator for SpecPskIdentityCombinator {
    type SpecResult = SpecPskIdentity;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentityCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentityCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentityCombinatorAlias = Mapped<(SpecOpaque1FfffCombinator, U32Be), PskIdentityMapper>;

pub struct PskIdentityCombinator(PskIdentityCombinatorAlias);

impl View for PskIdentityCombinator {
    type V = SpecPskIdentityCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentityCombinator(self.0@) }
}
impl Combinator for PskIdentityCombinator {
    type Result<'a> = PskIdentity<'a>;
    type Owned = PskIdentityOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskIdentityCombinatorAlias = Mapped<(Opaque1FfffCombinator, U32Be), PskIdentityMapper>;


pub struct SpecPskIdentitiesIdentitiesCombinator(SpecPskIdentitiesIdentitiesCombinatorAlias);

impl SpecCombinator for SpecPskIdentitiesIdentitiesCombinator {
    type SpecResult = SpecPskIdentitiesIdentities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentitiesIdentitiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentitiesIdentitiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentitiesIdentitiesCombinatorAlias = AndThen<Bytes, Repeat<SpecPskIdentityCombinator>>;

pub struct PskIdentitiesIdentitiesCombinator(PskIdentitiesIdentitiesCombinatorAlias);

impl View for PskIdentitiesIdentitiesCombinator {
    type V = SpecPskIdentitiesIdentitiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentitiesIdentitiesCombinator(self.0@) }
}
impl Combinator for PskIdentitiesIdentitiesCombinator {
    type Result<'a> = PskIdentitiesIdentities<'a>;
    type Owned = PskIdentitiesIdentitiesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskIdentitiesIdentitiesCombinatorAlias = AndThen<Bytes, Repeat<PskIdentityCombinator>>;

impl SpecPred for Predicate17762240283561303569 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 7 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecPskIdentitiesCombinator(SpecPskIdentitiesCombinatorAlias);

impl SpecCombinator for SpecPskIdentitiesCombinator {
    type SpecResult = SpecPskIdentities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskIdentitiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskIdentitiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskIdentitiesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate17762240283561303569>, SpecPskIdentitiesIdentitiesCombinator>, PskIdentitiesMapper>;
pub struct Predicate17762240283561303569;
impl View for Predicate17762240283561303569 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17762240283561303569 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 7 && i <= 65535) {
            true
        } else {
            false
        }
    }
}
pub struct PskIdentitiesCont;
pub struct PskIdentitiesCombinator(PskIdentitiesCombinatorAlias);

impl View for PskIdentitiesCombinator {
    type V = SpecPskIdentitiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskIdentitiesCombinator(self.0@) }
}
impl Combinator for PskIdentitiesCombinator {
    type Result<'a> = PskIdentities<'a>;
    type Owned = PskIdentitiesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskIdentitiesCombinatorAlias = Mapped<Depend<Refined<U16Be, Predicate17762240283561303569>, PskIdentitiesIdentitiesCombinator, PskIdentitiesCont>, PskIdentitiesMapper>;

impl SpecPred for Predicate14956021864372697443 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 32 && i <= 255) {
            true
        } else {
            false
        }
    }
}

pub struct SpecPskBinderEntryCombinator(SpecPskBinderEntryCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntryCombinator {
    type SpecResult = SpecPskBinderEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntryCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate14956021864372697443>, Bytes>, PskBinderEntryMapper>;
pub struct Predicate14956021864372697443;
impl View for Predicate14956021864372697443 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14956021864372697443 {
    type Input<'a> = u8;
    type InputOwned = u8;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 32 && i <= 255) {
            true
        } else {
            false
        }
    }
}
pub struct PskBinderEntryCont;
pub struct PskBinderEntryCombinator(PskBinderEntryCombinatorAlias);

impl View for PskBinderEntryCombinator {
    type V = SpecPskBinderEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntryCombinator(self.0@) }
}
impl Combinator for PskBinderEntryCombinator {
    type Result<'a> = PskBinderEntry<'a>;
    type Owned = PskBinderEntryOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskBinderEntryCombinatorAlias = Mapped<Depend<Refined<U8, Predicate14956021864372697443>, Bytes, PskBinderEntryCont>, PskBinderEntryMapper>;


pub struct SpecPskBinderEntriesBindersCombinator(SpecPskBinderEntriesBindersCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntriesBindersCombinator {
    type SpecResult = SpecPskBinderEntriesBinders;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntriesBindersCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntriesBindersCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntriesBindersCombinatorAlias = AndThen<Bytes, Repeat<SpecPskBinderEntryCombinator>>;

pub struct PskBinderEntriesBindersCombinator(PskBinderEntriesBindersCombinatorAlias);

impl View for PskBinderEntriesBindersCombinator {
    type V = SpecPskBinderEntriesBindersCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntriesBindersCombinator(self.0@) }
}
impl Combinator for PskBinderEntriesBindersCombinator {
    type Result<'a> = PskBinderEntriesBinders<'a>;
    type Owned = PskBinderEntriesBindersOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskBinderEntriesBindersCombinatorAlias = AndThen<Bytes, Repeat<PskBinderEntryCombinator>>;

impl SpecPred for Predicate14504484746533333987 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 33 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecPskBinderEntriesCombinator(SpecPskBinderEntriesCombinatorAlias);

impl SpecCombinator for SpecPskBinderEntriesCombinator {
    type SpecResult = SpecPskBinderEntries;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskBinderEntriesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskBinderEntriesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskBinderEntriesCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate14504484746533333987>, SpecPskBinderEntriesBindersCombinator>, PskBinderEntriesMapper>;
pub struct Predicate14504484746533333987;
impl View for Predicate14504484746533333987 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate14504484746533333987 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 33 && i <= 65535) {
            true
        } else {
            false
        }
    }
}
pub struct PskBinderEntriesCont;
pub struct PskBinderEntriesCombinator(PskBinderEntriesCombinatorAlias);

impl View for PskBinderEntriesCombinator {
    type V = SpecPskBinderEntriesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskBinderEntriesCombinator(self.0@) }
}
impl Combinator for PskBinderEntriesCombinator {
    type Result<'a> = PskBinderEntries<'a>;
    type Owned = PskBinderEntriesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskBinderEntriesCombinatorAlias = Mapped<Depend<Refined<U16Be, Predicate14504484746533333987>, PskBinderEntriesBindersCombinator, PskBinderEntriesCont>, PskBinderEntriesMapper>;


pub struct SpecOfferedPsksCombinator(SpecOfferedPsksCombinatorAlias);

impl SpecCombinator for SpecOfferedPsksCombinator {
    type SpecResult = SpecOfferedPsks;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOfferedPsksCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOfferedPsksCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOfferedPsksCombinatorAlias = Mapped<(SpecPskIdentitiesCombinator, SpecPskBinderEntriesCombinator), OfferedPsksMapper>;

pub struct OfferedPsksCombinator(OfferedPsksCombinatorAlias);

impl View for OfferedPsksCombinator {
    type V = SpecOfferedPsksCombinator;
    closed spec fn view(&self) -> Self::V { SpecOfferedPsksCombinator(self.0@) }
}
impl Combinator for OfferedPsksCombinator {
    type Result<'a> = OfferedPsks<'a>;
    type Owned = OfferedPsksOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OfferedPsksCombinatorAlias = Mapped<(PskIdentitiesCombinator, PskBinderEntriesCombinator), OfferedPsksMapper>;


pub struct SpecPreSharedKeyClientExtensionCombinator(SpecPreSharedKeyClientExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    type SpecResult = SpecPreSharedKeyClientExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPreSharedKeyClientExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyClientExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPreSharedKeyClientExtensionCombinatorAlias = Mapped<SpecOfferedPsksCombinator, PreSharedKeyClientExtensionMapper>;

pub struct PreSharedKeyClientExtensionCombinator(PreSharedKeyClientExtensionCombinatorAlias);

impl View for PreSharedKeyClientExtensionCombinator {
    type V = SpecPreSharedKeyClientExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyClientExtensionCombinator(self.0@) }
}
impl Combinator for PreSharedKeyClientExtensionCombinator {
    type Result<'a> = PreSharedKeyClientExtension<'a>;
    type Owned = PreSharedKeyClientExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PreSharedKeyClientExtensionCombinatorAlias = Mapped<OfferedPsksCombinator, PreSharedKeyClientExtensionMapper>;

impl SpecPred for Predicate12026843412570934212 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 254) {
            true
        } else {
            false
        }
    }
}

pub struct SpecSupportedVersionsClientCombinator(SpecSupportedVersionsClientCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsClientCombinator {
    type SpecResult = SpecSupportedVersionsClient;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsClientCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsClientCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsClientCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate12026843412570934212>, SpecSupportedVersionsClientVersionsCombinator>, SupportedVersionsClientMapper>;
pub struct Predicate12026843412570934212;
impl View for Predicate12026843412570934212 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate12026843412570934212 {
    type Input<'a> = u8;
    type InputOwned = u8;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 2 && i <= 254) {
            true
        } else {
            false
        }
    }
}
pub struct SupportedVersionsClientCont;
pub struct SupportedVersionsClientCombinator(SupportedVersionsClientCombinatorAlias);

impl View for SupportedVersionsClientCombinator {
    type V = SpecSupportedVersionsClientCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsClientCombinator(self.0@) }
}
impl Combinator for SupportedVersionsClientCombinator {
    type Result<'a> = SupportedVersionsClient;
    type Owned = SupportedVersionsClientOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SupportedVersionsClientCombinatorAlias = Mapped<Depend<Refined<U8, Predicate12026843412570934212>, SupportedVersionsClientVersionsCombinator, SupportedVersionsClientCont>, SupportedVersionsClientMapper>;


pub struct SpecCookieCombinator(SpecCookieCombinatorAlias);

impl SpecCombinator for SpecCookieCombinator {
    type SpecResult = SpecCookie;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCookieCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCookieCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCookieCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct CookieCombinator(CookieCombinatorAlias);

impl View for CookieCombinator {
    type V = SpecCookieCombinator;
    closed spec fn view(&self) -> Self::V { SpecCookieCombinator(self.0@) }
}
impl Combinator for CookieCombinator {
    type Result<'a> = Cookie<'a>;
    type Owned = CookieOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CookieCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecPskKeyExchangeModesCombinator(SpecPskKeyExchangeModesCombinatorAlias);

impl SpecCombinator for SpecPskKeyExchangeModesCombinator {
    type SpecResult = SpecPskKeyExchangeModes;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPskKeyExchangeModesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPskKeyExchangeModesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPskKeyExchangeModesCombinatorAlias = Mapped<SpecDepend<SpecUint1FfCombinator, SpecPskKeyExchangeModesModesCombinator>, PskKeyExchangeModesMapper>;
pub struct PskKeyExchangeModesCont;
pub struct PskKeyExchangeModesCombinator(PskKeyExchangeModesCombinatorAlias);

impl View for PskKeyExchangeModesCombinator {
    type V = SpecPskKeyExchangeModesCombinator;
    closed spec fn view(&self) -> Self::V { SpecPskKeyExchangeModesCombinator(self.0@) }
}
impl Combinator for PskKeyExchangeModesCombinator {
    type Result<'a> = PskKeyExchangeModes;
    type Owned = PskKeyExchangeModesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PskKeyExchangeModesCombinatorAlias = Mapped<Depend<Uint1FfCombinator, PskKeyExchangeModesModesCombinator, PskKeyExchangeModesCont>, PskKeyExchangeModesMapper>;


pub struct SpecDistinguishedNameCombinator(SpecDistinguishedNameCombinatorAlias);

impl SpecCombinator for SpecDistinguishedNameCombinator {
    type SpecResult = SpecDistinguishedName;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecDistinguishedNameCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecDistinguishedNameCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecDistinguishedNameCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct DistinguishedNameCombinator(DistinguishedNameCombinatorAlias);

impl View for DistinguishedNameCombinator {
    type V = SpecDistinguishedNameCombinator;
    closed spec fn view(&self) -> Self::V { SpecDistinguishedNameCombinator(self.0@) }
}
impl Combinator for DistinguishedNameCombinator {
    type Result<'a> = DistinguishedName<'a>;
    type Owned = DistinguishedNameOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type DistinguishedNameCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias);

impl SpecCombinator for SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    type SpecResult = SpecCertificateAuthoritiesExtensionAuthorities;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateAuthoritiesExtensionAuthoritiesCombinatorAlias = AndThen<Bytes, Repeat<SpecDistinguishedNameCombinator>>;

pub struct CertificateAuthoritiesExtensionAuthoritiesCombinator(CertificateAuthoritiesExtensionAuthoritiesCombinatorAlias);

impl View for CertificateAuthoritiesExtensionAuthoritiesCombinator {
    type V = SpecCertificateAuthoritiesExtensionAuthoritiesCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(self.0@) }
}
impl Combinator for CertificateAuthoritiesExtensionAuthoritiesCombinator {
    type Result<'a> = CertificateAuthoritiesExtensionAuthorities<'a>;
    type Owned = CertificateAuthoritiesExtensionAuthoritiesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateAuthoritiesExtensionAuthoritiesCombinatorAlias = AndThen<Bytes, Repeat<DistinguishedNameCombinator>>;

impl SpecPred for Predicate17709910934222271310 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 3 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecCertificateAuthoritiesExtensionCombinator(SpecCertificateAuthoritiesExtensionCombinatorAlias);

impl SpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    type SpecResult = SpecCertificateAuthoritiesExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateAuthoritiesExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateAuthoritiesExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateAuthoritiesExtensionCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate17709910934222271310>, SpecCertificateAuthoritiesExtensionAuthoritiesCombinator>, CertificateAuthoritiesExtensionMapper>;
pub struct Predicate17709910934222271310;
impl View for Predicate17709910934222271310 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate17709910934222271310 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 3 && i <= 65535) {
            true
        } else {
            false
        }
    }
}
pub struct CertificateAuthoritiesExtensionCont;
pub struct CertificateAuthoritiesExtensionCombinator(CertificateAuthoritiesExtensionCombinatorAlias);

impl View for CertificateAuthoritiesExtensionCombinator {
    type V = SpecCertificateAuthoritiesExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateAuthoritiesExtensionCombinator(self.0@) }
}
impl Combinator for CertificateAuthoritiesExtensionCombinator {
    type Result<'a> = CertificateAuthoritiesExtension<'a>;
    type Owned = CertificateAuthoritiesExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateAuthoritiesExtensionCombinatorAlias = Mapped<Depend<Refined<U16Be, Predicate17709910934222271310>, CertificateAuthoritiesExtensionAuthoritiesCombinator, CertificateAuthoritiesExtensionCont>, CertificateAuthoritiesExtensionMapper>;


pub struct SpecOidFilterCombinator(SpecOidFilterCombinatorAlias);

impl SpecCombinator for SpecOidFilterCombinator {
    type SpecResult = SpecOidFilter;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterCombinatorAlias = Mapped<(SpecOpaque1FfCombinator, SpecOpaque0FfffCombinator), OidFilterMapper>;

pub struct OidFilterCombinator(OidFilterCombinatorAlias);

impl View for OidFilterCombinator {
    type V = SpecOidFilterCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterCombinator(self.0@) }
}
impl Combinator for OidFilterCombinator {
    type Result<'a> = OidFilter<'a>;
    type Owned = OidFilterOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OidFilterCombinatorAlias = Mapped<(Opaque1FfCombinator, Opaque0FfffCombinator), OidFilterMapper>;


pub struct SpecOidFilterExtensionFiltersCombinator(SpecOidFilterExtensionFiltersCombinatorAlias);

impl SpecCombinator for SpecOidFilterExtensionFiltersCombinator {
    type SpecResult = SpecOidFilterExtensionFilters;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterExtensionFiltersCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterExtensionFiltersCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterExtensionFiltersCombinatorAlias = AndThen<Bytes, Repeat<SpecOidFilterCombinator>>;

pub struct OidFilterExtensionFiltersCombinator(OidFilterExtensionFiltersCombinatorAlias);

impl View for OidFilterExtensionFiltersCombinator {
    type V = SpecOidFilterExtensionFiltersCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterExtensionFiltersCombinator(self.0@) }
}
impl Combinator for OidFilterExtensionFiltersCombinator {
    type Result<'a> = OidFilterExtensionFilters<'a>;
    type Owned = OidFilterExtensionFiltersOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OidFilterExtensionFiltersCombinatorAlias = AndThen<Bytes, Repeat<OidFilterCombinator>>;


pub struct SpecOidFilterExtensionCombinator(SpecOidFilterExtensionCombinatorAlias);

impl SpecCombinator for SpecOidFilterExtensionCombinator {
    type SpecResult = SpecOidFilterExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOidFilterExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOidFilterExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOidFilterExtensionCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecOidFilterExtensionFiltersCombinator>, OidFilterExtensionMapper>;
pub struct OidFilterExtensionCont;
pub struct OidFilterExtensionCombinator(OidFilterExtensionCombinatorAlias);

impl View for OidFilterExtensionCombinator {
    type V = SpecOidFilterExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecOidFilterExtensionCombinator(self.0@) }
}
impl Combinator for OidFilterExtensionCombinator {
    type Result<'a> = OidFilterExtension<'a>;
    type Owned = OidFilterExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OidFilterExtensionCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, OidFilterExtensionFiltersCombinator, OidFilterExtensionCont>, OidFilterExtensionMapper>;

pub const UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation32Combinator(SpecUncompressedPointRepresentation32CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation32Combinator {
    type SpecResult = SpecUncompressedPointRepresentation32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation32CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<32>, BytesN<32>)), UncompressedPointRepresentation32Mapper>;

pub struct UncompressedPointRepresentation32Combinator(UncompressedPointRepresentation32CombinatorAlias);

impl View for UncompressedPointRepresentation32Combinator {
    type V = SpecUncompressedPointRepresentation32Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation32Combinator(self.0@) }
}
impl Combinator for UncompressedPointRepresentation32Combinator {
    type Result<'a> = UncompressedPointRepresentation32<'a>;
    type Owned = UncompressedPointRepresentation32Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UncompressedPointRepresentation32CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<32>, BytesN<32>)), UncompressedPointRepresentation32Mapper>;

pub const UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation48Combinator(SpecUncompressedPointRepresentation48CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation48Combinator {
    type SpecResult = SpecUncompressedPointRepresentation48;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation48Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation48CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation48CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<48>, BytesN<48>)), UncompressedPointRepresentation48Mapper>;

pub struct UncompressedPointRepresentation48Combinator(UncompressedPointRepresentation48CombinatorAlias);

impl View for UncompressedPointRepresentation48Combinator {
    type V = SpecUncompressedPointRepresentation48Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation48Combinator(self.0@) }
}
impl Combinator for UncompressedPointRepresentation48Combinator {
    type Result<'a> = UncompressedPointRepresentation48<'a>;
    type Owned = UncompressedPointRepresentation48Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UncompressedPointRepresentation48CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<48>, BytesN<48>)), UncompressedPointRepresentation48Mapper>;

pub const UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM: u8 = 4;

pub struct SpecUncompressedPointRepresentation66Combinator(SpecUncompressedPointRepresentation66CombinatorAlias);

impl SpecCombinator for SpecUncompressedPointRepresentation66Combinator {
    type SpecResult = SpecUncompressedPointRepresentation66;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUncompressedPointRepresentation66Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUncompressedPointRepresentation66CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUncompressedPointRepresentation66CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<66>, BytesN<66>)), UncompressedPointRepresentation66Mapper>;

pub struct UncompressedPointRepresentation66Combinator(UncompressedPointRepresentation66CombinatorAlias);

impl View for UncompressedPointRepresentation66Combinator {
    type V = SpecUncompressedPointRepresentation66Combinator;
    closed spec fn view(&self) -> Self::V { SpecUncompressedPointRepresentation66Combinator(self.0@) }
}
impl Combinator for UncompressedPointRepresentation66Combinator {
    type Result<'a> = UncompressedPointRepresentation66<'a>;
    type Owned = UncompressedPointRepresentation66Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UncompressedPointRepresentation66CombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, (BytesN<66>, BytesN<66>)), UncompressedPointRepresentation66Mapper>;


pub struct SpecMontgomeryPoint32Combinator(SpecMontgomeryPoint32CombinatorAlias);

impl SpecCombinator for SpecMontgomeryPoint32Combinator {
    type SpecResult = SpecMontgomeryPoint32;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMontgomeryPoint32Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMontgomeryPoint32CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMontgomeryPoint32CombinatorAlias = BytesN<32>;

pub struct MontgomeryPoint32Combinator(MontgomeryPoint32CombinatorAlias);

impl View for MontgomeryPoint32Combinator {
    type V = SpecMontgomeryPoint32Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryPoint32Combinator(self.0@) }
}
impl Combinator for MontgomeryPoint32Combinator {
    type Result<'a> = MontgomeryPoint32<'a>;
    type Owned = MontgomeryPoint32Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type MontgomeryPoint32CombinatorAlias = BytesN<32>;


pub struct SpecMontgomeryForm56Combinator(SpecMontgomeryForm56CombinatorAlias);

impl SpecCombinator for SpecMontgomeryForm56Combinator {
    type SpecResult = SpecMontgomeryForm56;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecMontgomeryForm56Combinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecMontgomeryForm56CombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecMontgomeryForm56CombinatorAlias = BytesN<56>;

pub struct MontgomeryForm56Combinator(MontgomeryForm56CombinatorAlias);

impl View for MontgomeryForm56Combinator {
    type V = SpecMontgomeryForm56Combinator;
    closed spec fn view(&self) -> Self::V { SpecMontgomeryForm56Combinator(self.0@) }
}
impl Combinator for MontgomeryForm56Combinator {
    type Result<'a> = MontgomeryForm56<'a>;
    type Owned = MontgomeryForm56Owned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type MontgomeryForm56CombinatorAlias = BytesN<56>;


pub struct SpecSeverDhParamsCombinator(SpecSeverDhParamsCombinatorAlias);

impl SpecCombinator for SpecSeverDhParamsCombinator {
    type SpecResult = SpecSeverDhParams;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverDhParamsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverDhParamsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverDhParamsCombinatorAlias = Mapped<(SpecOpaque1FfffCombinator, (SpecOpaque1FfffCombinator, SpecOpaque1FfffCombinator)), SeverDhParamsMapper>;

pub struct SeverDhParamsCombinator(SeverDhParamsCombinatorAlias);

impl View for SeverDhParamsCombinator {
    type V = SpecSeverDhParamsCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverDhParamsCombinator(self.0@) }
}
impl Combinator for SeverDhParamsCombinator {
    type Result<'a> = SeverDhParams<'a>;
    type Owned = SeverDhParamsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SeverDhParamsCombinatorAlias = Mapped<(Opaque1FfffCombinator, (Opaque1FfffCombinator, Opaque1FfffCombinator)), SeverDhParamsMapper>;


pub struct SpecKeyExchangeDataCombinator(SpecKeyExchangeDataCombinatorAlias);

impl SpecCombinator for SpecKeyExchangeDataCombinator {
    type SpecResult = SpecKeyExchangeData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyExchangeDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyExchangeDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyExchangeDataCombinatorAlias = SpecOpaque1FfffCombinator;

pub struct KeyExchangeDataCombinator(KeyExchangeDataCombinatorAlias);

impl View for KeyExchangeDataCombinator {
    type V = SpecKeyExchangeDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyExchangeDataCombinator(self.0@) }
}
impl Combinator for KeyExchangeDataCombinator {
    type Result<'a> = KeyExchangeData<'a>;
    type Owned = KeyExchangeDataOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyExchangeDataCombinatorAlias = Opaque1FfffCombinator;


pub struct SpecKeyShareEntryKeyExchangeCombinator(SpecKeyShareEntryKeyExchangeCombinatorAlias);

impl SpecCombinator for SpecKeyShareEntryKeyExchangeCombinator {
    type SpecResult = SpecKeyShareEntryKeyExchange;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareEntryKeyExchangeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareEntryKeyExchangeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareEntryKeyExchangeCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecUncompressedPointRepresentation32Combinator>, OrdChoice<Cond<SpecUncompressedPointRepresentation48Combinator>, OrdChoice<Cond<SpecUncompressedPointRepresentation66Combinator>, OrdChoice<Cond<SpecMontgomeryPoint32Combinator>, OrdChoice<Cond<SpecMontgomeryForm56Combinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, OrdChoice<Cond<SpecSeverDhParamsCombinator>, Cond<SpecKeyExchangeDataCombinator>>>>>>>>>>>, KeyShareEntryKeyExchangeMapper>>;

pub struct KeyShareEntryKeyExchangeCombinator(KeyShareEntryKeyExchangeCombinatorAlias);

impl View for KeyShareEntryKeyExchangeCombinator {
    type V = SpecKeyShareEntryKeyExchangeCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareEntryKeyExchangeCombinator(self.0@) }
}
impl Combinator for KeyShareEntryKeyExchangeCombinator {
    type Result<'a> = KeyShareEntryKeyExchange<'a>;
    type Owned = KeyShareEntryKeyExchangeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyShareEntryKeyExchangeCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<UncompressedPointRepresentation32Combinator>, OrdChoice<Cond<UncompressedPointRepresentation48Combinator>, OrdChoice<Cond<UncompressedPointRepresentation66Combinator>, OrdChoice<Cond<MontgomeryPoint32Combinator>, OrdChoice<Cond<MontgomeryForm56Combinator>, OrdChoice<Cond<SeverDhParamsCombinator>, OrdChoice<Cond<SeverDhParamsCombinator>, OrdChoice<Cond<SeverDhParamsCombinator>, OrdChoice<Cond<SeverDhParamsCombinator>, OrdChoice<Cond<SeverDhParamsCombinator>, Cond<KeyExchangeDataCombinator>>>>>>>>>>>, KeyShareEntryKeyExchangeMapper>>;


pub struct SpecKeyShareEntryCombinator(SpecKeyShareEntryCombinatorAlias);

impl SpecCombinator for SpecKeyShareEntryCombinator {
    type SpecResult = SpecKeyShareEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareEntryCombinatorAlias = Mapped<SpecDepend<(SpecNamedGroupCombinator, SpecUint1FfffCombinator), SpecKeyShareEntryKeyExchangeCombinator>, KeyShareEntryMapper>;
pub struct KeyShareEntryCont;
pub struct KeyShareEntryCombinator(KeyShareEntryCombinatorAlias);

impl View for KeyShareEntryCombinator {
    type V = SpecKeyShareEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareEntryCombinator(self.0@) }
}
impl Combinator for KeyShareEntryCombinator {
    type Result<'a> = KeyShareEntry<'a>;
    type Owned = KeyShareEntryOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyShareEntryCombinatorAlias = Mapped<Depend<(NamedGroupCombinator, Uint1FfffCombinator), KeyShareEntryKeyExchangeCombinator, KeyShareEntryCont>, KeyShareEntryMapper>;


pub struct SpecKeyShareClientHelloClientSharesCombinator(SpecKeyShareClientHelloClientSharesCombinatorAlias);

impl SpecCombinator for SpecKeyShareClientHelloClientSharesCombinator {
    type SpecResult = SpecKeyShareClientHelloClientShares;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareClientHelloClientSharesCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareClientHelloClientSharesCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareClientHelloClientSharesCombinatorAlias = AndThen<Bytes, Repeat<SpecKeyShareEntryCombinator>>;

pub struct KeyShareClientHelloClientSharesCombinator(KeyShareClientHelloClientSharesCombinatorAlias);

impl View for KeyShareClientHelloClientSharesCombinator {
    type V = SpecKeyShareClientHelloClientSharesCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareClientHelloClientSharesCombinator(self.0@) }
}
impl Combinator for KeyShareClientHelloClientSharesCombinator {
    type Result<'a> = KeyShareClientHelloClientShares<'a>;
    type Owned = KeyShareClientHelloClientSharesOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyShareClientHelloClientSharesCombinatorAlias = AndThen<Bytes, Repeat<KeyShareEntryCombinator>>;


pub struct SpecKeyShareClientHelloCombinator(SpecKeyShareClientHelloCombinatorAlias);

impl SpecCombinator for SpecKeyShareClientHelloCombinator {
    type SpecResult = SpecKeyShareClientHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyShareClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyShareClientHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyShareClientHelloCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecKeyShareClientHelloClientSharesCombinator>, KeyShareClientHelloMapper>;
pub struct KeyShareClientHelloCont;
pub struct KeyShareClientHelloCombinator(KeyShareClientHelloCombinatorAlias);

impl View for KeyShareClientHelloCombinator {
    type V = SpecKeyShareClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyShareClientHelloCombinator(self.0@) }
}
impl Combinator for KeyShareClientHelloCombinator {
    type Result<'a> = KeyShareClientHello<'a>;
    type Owned = KeyShareClientHelloOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyShareClientHelloCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, KeyShareClientHelloClientSharesCombinator, KeyShareClientHelloCont>, KeyShareClientHelloMapper>;


pub struct SpecClientHelloExtensionExtensionDataCombinator(SpecClientHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    type SpecResult = SpecClientHelloExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecServerNameListCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecCertificateStatusRequestCombinator>, OrdChoice<Cond<SpecNamedGroupListCombinator>, OrdChoice<Cond<SpecEcPointFormatListCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecUseSrtpDataCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecPaddingExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<Bytes>, OrdChoice<Cond<SpecPreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSupportedVersionsClientCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecPskKeyExchangeModesCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecKeyShareClientHelloCombinator>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper>>;

pub struct ClientHelloExtensionExtensionDataCombinator(ClientHelloExtensionExtensionDataCombinatorAlias);

impl View for ClientHelloExtensionExtensionDataCombinator {
    type V = SpecClientHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionExtensionDataCombinator(self.0@) }
}
impl Combinator for ClientHelloExtensionExtensionDataCombinator {
    type Result<'a> = ClientHelloExtensionExtensionData<'a>;
    type Owned = ClientHelloExtensionExtensionDataOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<ServerNameListCombinator>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<CertificateStatusRequestCombinator>, OrdChoice<Cond<NamedGroupListCombinator>, OrdChoice<Cond<EcPointFormatListCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator>, OrdChoice<Cond<UseSrtpDataCombinator>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator>, OrdChoice<Cond<SignedCertificateTimestampListCombinator>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<PaddingExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<Bytes>, OrdChoice<Cond<PreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SupportedVersionsClientCombinator>, OrdChoice<Cond<CookieCombinator>, OrdChoice<Cond<PskKeyExchangeModesCombinator>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<OidFilterExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator>, OrdChoice<Cond<KeyShareClientHelloCombinator>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>>, ClientHelloExtensionExtensionDataMapper>>;

impl SpecPred for Predicate184937773087435626 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

pub struct SpecUint0FffeCombinator(SpecUint0FffeCombinatorAlias);

impl SpecCombinator for SpecUint0FffeCombinator {
    type SpecResult = SpecUint0Fffe;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUint0FffeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUint0FffeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUint0FffeCombinatorAlias = Refined<U16Be, Predicate184937773087435626>;
pub struct Predicate184937773087435626;
impl View for Predicate184937773087435626 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate184937773087435626 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 65534) {
            true
        } else {
            false
        }
    }
}

pub struct Uint0FffeCombinator(Uint0FffeCombinatorAlias);

impl View for Uint0FffeCombinator {
    type V = SpecUint0FffeCombinator;
    closed spec fn view(&self) -> Self::V { SpecUint0FffeCombinator(self.0@) }
}
impl Combinator for Uint0FffeCombinator {
    type Result<'a> = Uint0Fffe;
    type Owned = Uint0FffeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Uint0FffeCombinatorAlias = Refined<U16Be, Predicate184937773087435626>;


pub struct SpecKeyUpdateRequestCombinator(SpecKeyUpdateRequestCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateRequestCombinator {
    type SpecResult = SpecKeyUpdateRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyUpdateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyUpdateRequestCombinatorAlias = TryMap<U8, KeyUpdateRequestMapper>;

pub struct KeyUpdateRequestCombinator(KeyUpdateRequestCombinatorAlias);

impl View for KeyUpdateRequestCombinator {
    type V = SpecKeyUpdateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateRequestCombinator(self.0@) }
}
impl Combinator for KeyUpdateRequestCombinator {
    type Result<'a> = KeyUpdateRequest;
    type Owned = KeyUpdateRequestOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyUpdateRequestCombinatorAlias = TryMap<U8, KeyUpdateRequestMapper>;


pub struct SpecKeyUpdateCombinator(SpecKeyUpdateCombinatorAlias);

impl SpecCombinator for SpecKeyUpdateCombinator {
    type SpecResult = SpecKeyUpdate;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecKeyUpdateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecKeyUpdateCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecKeyUpdateCombinatorAlias = Mapped<SpecKeyUpdateRequestCombinator, KeyUpdateMapper>;

pub struct KeyUpdateCombinator(KeyUpdateCombinatorAlias);

impl View for KeyUpdateCombinator {
    type V = SpecKeyUpdateCombinator;
    closed spec fn view(&self) -> Self::V { SpecKeyUpdateCombinator(self.0@) }
}
impl Combinator for KeyUpdateCombinator {
    type Result<'a> = KeyUpdate;
    type Owned = KeyUpdateOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type KeyUpdateCombinatorAlias = Mapped<KeyUpdateRequestCombinator, KeyUpdateMapper>;


pub struct SpecSupportedVersionsServerCombinator(SpecSupportedVersionsServerCombinatorAlias);

impl SpecCombinator for SpecSupportedVersionsServerCombinator {
    type SpecResult = SpecSupportedVersionsServer;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSupportedVersionsServerCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSupportedVersionsServerCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSupportedVersionsServerCombinatorAlias = Mapped<SpecProtocolVersionCombinator, SupportedVersionsServerMapper>;

pub struct SupportedVersionsServerCombinator(SupportedVersionsServerCombinatorAlias);

impl View for SupportedVersionsServerCombinator {
    type V = SpecSupportedVersionsServerCombinator;
    closed spec fn view(&self) -> Self::V { SpecSupportedVersionsServerCombinator(self.0@) }
}
impl Combinator for SupportedVersionsServerCombinator {
    type Result<'a> = SupportedVersionsServer;
    type Owned = SupportedVersionsServerOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SupportedVersionsServerCombinatorAlias = Mapped<ProtocolVersionCombinator, SupportedVersionsServerMapper>;

impl SpecPred for Predicate10565972399076720534 {
    type Input = u24;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i).spec_as_u32();
        if (i >= 1 && i <= 16777215) {
            true
        } else {
            false
        }
    }
}

pub struct SpecOpaque1FfffffCombinator(SpecOpaque1FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque1FfffffCombinator {
    type SpecResult = SpecOpaque1Ffffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque1FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque1FfffffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque1FfffffCombinatorAlias = Mapped<SpecDepend<Refined<U24Be, Predicate10565972399076720534>, Bytes>, Opaque1FfffffMapper>;
pub struct Predicate10565972399076720534;
impl View for Predicate10565972399076720534 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate10565972399076720534 {
    type Input<'a> = u24;
    type InputOwned = u24;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i).as_u32();
        if (i >= 1 && i <= 16777215) {
            true
        } else {
            false
        }
    }
}
pub struct Opaque1FfffffCont;
pub struct Opaque1FfffffCombinator(Opaque1FfffffCombinatorAlias);

impl View for Opaque1FfffffCombinator {
    type V = SpecOpaque1FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque1FfffffCombinator(self.0@) }
}
impl Combinator for Opaque1FfffffCombinator {
    type Result<'a> = Opaque1Ffffff<'a>;
    type Owned = Opaque1FfffffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque1FfffffCombinatorAlias = Mapped<Depend<Refined<U24Be, Predicate10565972399076720534>, Bytes, Opaque1FfffffCont>, Opaque1FfffffMapper>;


pub struct SpecEncryptedExtensionsExtensionsCombinator(SpecEncryptedExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionsExtensionsCombinator {
    type SpecResult = SpecEncryptedExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

pub struct EncryptedExtensionsExtensionsCombinator(EncryptedExtensionsExtensionsCombinatorAlias);

impl View for EncryptedExtensionsExtensionsCombinator {
    type V = SpecEncryptedExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionsExtensionsCombinator(self.0@) }
}
impl Combinator for EncryptedExtensionsExtensionsCombinator {
    type Result<'a> = EncryptedExtensionsExtensions<'a>;
    type Owned = EncryptedExtensionsExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EncryptedExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<ExtensionCombinator>>;


pub struct SpecEncryptedExtensionsCombinator(SpecEncryptedExtensionsCombinatorAlias);

impl SpecCombinator for SpecEncryptedExtensionsCombinator {
    type SpecResult = SpecEncryptedExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEncryptedExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEncryptedExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEncryptedExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint0FfffCombinator, SpecEncryptedExtensionsExtensionsCombinator>, EncryptedExtensionsMapper>;
pub struct EncryptedExtensionsCont;
pub struct EncryptedExtensionsCombinator(EncryptedExtensionsCombinatorAlias);

impl View for EncryptedExtensionsCombinator {
    type V = SpecEncryptedExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecEncryptedExtensionsCombinator(self.0@) }
}
impl Combinator for EncryptedExtensionsCombinator {
    type Result<'a> = EncryptedExtensions<'a>;
    type Owned = EncryptedExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EncryptedExtensionsCombinatorAlias = Mapped<Depend<Uint0FfffCombinator, EncryptedExtensionsExtensionsCombinator, EncryptedExtensionsCont>, EncryptedExtensionsMapper>;


pub struct SpecCertificateExtensionsCombinator(SpecCertificateExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateExtensionsCombinator {
    type SpecResult = SpecCertificateExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateExtensionsCombinatorAlias = SpecEncryptedExtensionsCombinator;

pub struct CertificateExtensionsCombinator(CertificateExtensionsCombinatorAlias);

impl View for CertificateExtensionsCombinator {
    type V = SpecCertificateExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateExtensionsCombinator(self.0@) }
}
impl Combinator for CertificateExtensionsCombinator {
    type Result<'a> = CertificateExtensions<'a>;
    type Owned = CertificateExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateExtensionsCombinatorAlias = EncryptedExtensionsCombinator;


pub struct SpecCertificateEntryCombinator(SpecCertificateEntryCombinatorAlias);

impl SpecCombinator for SpecCertificateEntryCombinator {
    type SpecResult = SpecCertificateEntry;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateEntryCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateEntryCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateEntryCombinatorAlias = Mapped<(SpecOpaque1FfffffCombinator, SpecCertificateExtensionsCombinator), CertificateEntryMapper>;

pub struct CertificateEntryCombinator(CertificateEntryCombinatorAlias);

impl View for CertificateEntryCombinator {
    type V = SpecCertificateEntryCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateEntryCombinator(self.0@) }
}
impl Combinator for CertificateEntryCombinator {
    type Result<'a> = CertificateEntry<'a>;
    type Owned = CertificateEntryOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateEntryCombinatorAlias = Mapped<(Opaque1FfffffCombinator, CertificateExtensionsCombinator), CertificateEntryMapper>;


pub struct SpecCertificateListListCombinator(SpecCertificateListListCombinatorAlias);

impl SpecCombinator for SpecCertificateListListCombinator {
    type SpecResult = SpecCertificateListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateListListCombinatorAlias = AndThen<Bytes, Repeat<SpecCertificateEntryCombinator>>;

pub struct CertificateListListCombinator(CertificateListListCombinatorAlias);

impl View for CertificateListListCombinator {
    type V = SpecCertificateListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateListListCombinator(self.0@) }
}
impl Combinator for CertificateListListCombinator {
    type Result<'a> = CertificateListList<'a>;
    type Owned = CertificateListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateListListCombinatorAlias = AndThen<Bytes, Repeat<CertificateEntryCombinator>>;


pub struct SpecCertificateListCombinator(SpecCertificateListCombinatorAlias);

impl SpecCombinator for SpecCertificateListCombinator {
    type SpecResult = SpecCertificateList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateListCombinatorAlias = Mapped<SpecDepend<U24Be, SpecCertificateListListCombinator>, CertificateListMapper>;
pub struct CertificateListCont;
pub struct CertificateListCombinator(CertificateListCombinatorAlias);

impl View for CertificateListCombinator {
    type V = SpecCertificateListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateListCombinator(self.0@) }
}
impl Combinator for CertificateListCombinator {
    type Result<'a> = CertificateList<'a>;
    type Owned = CertificateListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateListCombinatorAlias = Mapped<Depend<U24Be, CertificateListListCombinator, CertificateListCont>, CertificateListMapper>;


pub struct SpecCertificateCombinator(SpecCertificateCombinatorAlias);

impl SpecCombinator for SpecCertificateCombinator {
    type SpecResult = SpecCertificate;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateCombinatorAlias = Mapped<(SpecOpaque0FfCombinator, SpecCertificateListCombinator), CertificateMapper>;

pub struct CertificateCombinator(CertificateCombinatorAlias);

impl View for CertificateCombinator {
    type V = SpecCertificateCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateCombinator(self.0@) }
}
impl Combinator for CertificateCombinator {
    type Result<'a> = Certificate<'a>;
    type Owned = CertificateOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateCombinatorAlias = Mapped<(Opaque0FfCombinator, CertificateListCombinator), CertificateMapper>;


pub struct SpecEarlyDataIndicationNewSessionTicketCombinator(SpecEarlyDataIndicationNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    type SpecResult = SpecEarlyDataIndicationNewSessionTicket;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecEarlyDataIndicationNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecEarlyDataIndicationNewSessionTicketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecEarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;

pub struct EarlyDataIndicationNewSessionTicketCombinator(EarlyDataIndicationNewSessionTicketCombinatorAlias);

impl View for EarlyDataIndicationNewSessionTicketCombinator {
    type V = SpecEarlyDataIndicationNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecEarlyDataIndicationNewSessionTicketCombinator(self.0@) }
}
impl Combinator for EarlyDataIndicationNewSessionTicketCombinator {
    type Result<'a> = EarlyDataIndicationNewSessionTicket;
    type Owned = EarlyDataIndicationNewSessionTicketOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type EarlyDataIndicationNewSessionTicketCombinatorAlias = Mapped<U32Be, EarlyDataIndicationNewSessionTicketMapper>;


pub struct SpecPreSharedKeyServerExtensionCombinator(SpecPreSharedKeyServerExtensionCombinatorAlias);

impl SpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    type SpecResult = SpecPreSharedKeyServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecPreSharedKeyServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecPreSharedKeyServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecPreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;

pub struct PreSharedKeyServerExtensionCombinator(PreSharedKeyServerExtensionCombinatorAlias);

impl View for PreSharedKeyServerExtensionCombinator {
    type V = SpecPreSharedKeyServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecPreSharedKeyServerExtensionCombinator(self.0@) }
}
impl Combinator for PreSharedKeyServerExtensionCombinator {
    type Result<'a> = PreSharedKeyServerExtension;
    type Owned = PreSharedKeyServerExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type PreSharedKeyServerExtensionCombinatorAlias = Mapped<U16Be, PreSharedKeyServerExtensionMapper>;


pub struct SpecRandomCombinator(SpecRandomCombinatorAlias);

impl SpecCombinator for SpecRandomCombinator {
    type SpecResult = SpecRandom;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecRandomCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecRandomCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecRandomCombinatorAlias = BytesN<32>;

pub struct RandomCombinator(RandomCombinatorAlias);

impl View for RandomCombinator {
    type V = SpecRandomCombinator;
    closed spec fn view(&self) -> Self::V { SpecRandomCombinator(self.0@) }
}
impl Combinator for RandomCombinator {
    type Result<'a> = Random<'a>;
    type Owned = RandomOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type RandomCombinatorAlias = BytesN<32>;

impl SpecPred for Predicate10693986609604791304 {
    type Input = u8;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 32) {
            true
        } else {
            false
        }
    }
}

pub struct SpecSessionIdCombinator(SpecSessionIdCombinatorAlias);

impl SpecCombinator for SpecSessionIdCombinator {
    type SpecResult = SpecSessionId;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSessionIdCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSessionIdCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSessionIdCombinatorAlias = Mapped<SpecDepend<Refined<U8, Predicate10693986609604791304>, Bytes>, SessionIdMapper>;
pub struct Predicate10693986609604791304;
impl View for Predicate10693986609604791304 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate10693986609604791304 {
    type Input<'a> = u8;
    type InputOwned = u8;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 0 && i <= 32) {
            true
        } else {
            false
        }
    }
}
pub struct SessionIdCont;
pub struct SessionIdCombinator(SessionIdCombinatorAlias);

impl View for SessionIdCombinator {
    type V = SpecSessionIdCombinator;
    closed spec fn view(&self) -> Self::V { SpecSessionIdCombinator(self.0@) }
}
impl Combinator for SessionIdCombinator {
    type Result<'a> = SessionId<'a>;
    type Owned = SessionIdOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SessionIdCombinatorAlias = Mapped<Depend<Refined<U8, Predicate10693986609604791304>, Bytes, SessionIdCont>, SessionIdMapper>;


pub struct SpecCipherSuiteCombinator(SpecCipherSuiteCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteCombinator {
    type SpecResult = SpecCipherSuite;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteCombinatorAlias = U16Be;

pub struct CipherSuiteCombinator(CipherSuiteCombinatorAlias);

impl View for CipherSuiteCombinator {
    type V = SpecCipherSuiteCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteCombinator(self.0@) }
}
impl Combinator for CipherSuiteCombinator {
    type Result<'a> = CipherSuite;
    type Owned = CipherSuiteOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CipherSuiteCombinatorAlias = U16Be;


pub struct SpecCipherSuiteListListCombinator(SpecCipherSuiteListListCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteListListCombinator {
    type SpecResult = SpecCipherSuiteListList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteListListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteListListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteListListCombinatorAlias = AndThen<Bytes, Repeat<SpecCipherSuiteCombinator>>;

pub struct CipherSuiteListListCombinator(CipherSuiteListListCombinatorAlias);

impl View for CipherSuiteListListCombinator {
    type V = SpecCipherSuiteListListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteListListCombinator(self.0@) }
}
impl Combinator for CipherSuiteListListCombinator {
    type Result<'a> = CipherSuiteListList;
    type Owned = CipherSuiteListListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CipherSuiteListListCombinatorAlias = AndThen<Bytes, Repeat<CipherSuiteCombinator>>;


pub struct SpecCipherSuiteListCombinator(SpecCipherSuiteListCombinatorAlias);

impl SpecCombinator for SpecCipherSuiteListCombinator {
    type SpecResult = SpecCipherSuiteList;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCipherSuiteListCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCipherSuiteListCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCipherSuiteListCombinatorAlias = Mapped<SpecDepend<SpecUint2FffeCombinator, SpecCipherSuiteListListCombinator>, CipherSuiteListMapper>;
pub struct CipherSuiteListCont;
pub struct CipherSuiteListCombinator(CipherSuiteListCombinatorAlias);

impl View for CipherSuiteListCombinator {
    type V = SpecCipherSuiteListCombinator;
    closed spec fn view(&self) -> Self::V { SpecCipherSuiteListCombinator(self.0@) }
}
impl Combinator for CipherSuiteListCombinator {
    type Result<'a> = CipherSuiteList;
    type Owned = CipherSuiteListOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CipherSuiteListCombinatorAlias = Mapped<Depend<Uint2FffeCombinator, CipherSuiteListListCombinator, CipherSuiteListCont>, CipherSuiteListMapper>;


pub struct SpecClientHelloExtensionCombinator(SpecClientHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecClientHelloExtensionCombinator {
    type SpecResult = SpecClientHelloExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloExtensionCombinatorAlias = Mapped<SpecDepend<(SpecExtensionTypeCombinator, U16Be), SpecClientHelloExtensionExtensionDataCombinator>, ClientHelloExtensionMapper>;
pub struct ClientHelloExtensionCont;
pub struct ClientHelloExtensionCombinator(ClientHelloExtensionCombinatorAlias);

impl View for ClientHelloExtensionCombinator {
    type V = SpecClientHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloExtensionCombinator(self.0@) }
}
impl Combinator for ClientHelloExtensionCombinator {
    type Result<'a> = ClientHelloExtension<'a>;
    type Owned = ClientHelloExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientHelloExtensionCombinatorAlias = Mapped<Depend<(ExtensionTypeCombinator, U16Be), ClientHelloExtensionExtensionDataCombinator, ClientHelloExtensionCont>, ClientHelloExtensionMapper>;


pub struct SpecClientExtensionsExtensionsCombinator(SpecClientExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecClientExtensionsExtensionsCombinator {
    type SpecResult = SpecClientExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecClientHelloExtensionCombinator>>;

pub struct ClientExtensionsExtensionsCombinator(ClientExtensionsExtensionsCombinatorAlias);

impl View for ClientExtensionsExtensionsCombinator {
    type V = SpecClientExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientExtensionsExtensionsCombinator(self.0@) }
}
impl Combinator for ClientExtensionsExtensionsCombinator {
    type Result<'a> = ClientExtensionsExtensions<'a>;
    type Owned = ClientExtensionsExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<ClientHelloExtensionCombinator>>;

impl SpecPred for Predicate15770232246241775772 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 8 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecClientExtensionsCombinator(SpecClientExtensionsCombinatorAlias);

impl SpecCombinator for SpecClientExtensionsCombinator {
    type SpecResult = SpecClientExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate15770232246241775772>, SpecClientExtensionsExtensionsCombinator>, ClientExtensionsMapper>;
pub struct Predicate15770232246241775772;
impl View for Predicate15770232246241775772 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate15770232246241775772 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 8 && i <= 65535) {
            true
        } else {
            false
        }
    }
}
pub struct ClientExtensionsCont;
pub struct ClientExtensionsCombinator(ClientExtensionsCombinatorAlias);

impl View for ClientExtensionsCombinator {
    type V = SpecClientExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientExtensionsCombinator(self.0@) }
}
impl Combinator for ClientExtensionsCombinator {
    type Result<'a> = ClientExtensions<'a>;
    type Owned = ClientExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientExtensionsCombinatorAlias = Mapped<Depend<Refined<U16Be, Predicate15770232246241775772>, ClientExtensionsExtensionsCombinator, ClientExtensionsCont>, ClientExtensionsMapper>;


pub struct SpecClientHelloCombinator(SpecClientHelloCombinatorAlias);

impl SpecCombinator for SpecClientHelloCombinator {
    type SpecResult = SpecClientHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientHelloCombinatorAlias = Mapped<(SpecProtocolVersionCombinator, (SpecRandomCombinator, (SpecSessionIdCombinator, (SpecCipherSuiteListCombinator, (SpecOpaque1FfCombinator, SpecClientExtensionsCombinator))))), ClientHelloMapper>;

pub struct ClientHelloCombinator(ClientHelloCombinatorAlias);

impl View for ClientHelloCombinator {
    type V = SpecClientHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientHelloCombinator(self.0@) }
}
impl Combinator for ClientHelloCombinator {
    type Result<'a> = ClientHello<'a>;
    type Owned = ClientHelloOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientHelloCombinatorAlias = Mapped<(ProtocolVersionCombinator, (RandomCombinator, (SessionIdCombinator, (CipherSuiteListCombinator, (Opaque1FfCombinator, ClientExtensionsCombinator))))), ClientHelloMapper>;


pub struct SpecCertificateRequestExtensionsExtensionsCombinator(SpecCertificateRequestExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionsExtensionsCombinator {
    type SpecResult = SpecCertificateRequestExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecExtensionCombinator>>;

pub struct CertificateRequestExtensionsExtensionsCombinator(CertificateRequestExtensionsExtensionsCombinatorAlias);

impl View for CertificateRequestExtensionsExtensionsCombinator {
    type V = SpecCertificateRequestExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionsExtensionsCombinator(self.0@) }
}
impl Combinator for CertificateRequestExtensionsExtensionsCombinator {
    type Result<'a> = CertificateRequestExtensionsExtensions<'a>;
    type Owned = CertificateRequestExtensionsExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateRequestExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<ExtensionCombinator>>;


pub struct SpecCertificateRequestExtensionsCombinator(SpecCertificateRequestExtensionsCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestExtensionsCombinator {
    type SpecResult = SpecCertificateRequestExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, SpecCertificateRequestExtensionsExtensionsCombinator>, CertificateRequestExtensionsMapper>;
pub struct CertificateRequestExtensionsCont;
pub struct CertificateRequestExtensionsCombinator(CertificateRequestExtensionsCombinatorAlias);

impl View for CertificateRequestExtensionsCombinator {
    type V = SpecCertificateRequestExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestExtensionsCombinator(self.0@) }
}
impl Combinator for CertificateRequestExtensionsCombinator {
    type Result<'a> = CertificateRequestExtensions<'a>;
    type Owned = CertificateRequestExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateRequestExtensionsCombinatorAlias = Mapped<Depend<Uint2FfffCombinator, CertificateRequestExtensionsExtensionsCombinator, CertificateRequestExtensionsCont>, CertificateRequestExtensionsMapper>;


pub struct SpecCertificateRequestCombinator(SpecCertificateRequestCombinatorAlias);

impl SpecCombinator for SpecCertificateRequestCombinator {
    type SpecResult = SpecCertificateRequest;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateRequestCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateRequestCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateRequestCombinatorAlias = Mapped<(SpecOpaque0FfCombinator, SpecCertificateRequestExtensionsCombinator), CertificateRequestMapper>;

pub struct CertificateRequestCombinator(CertificateRequestCombinatorAlias);

impl View for CertificateRequestCombinator {
    type V = SpecCertificateRequestCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateRequestCombinator(self.0@) }
}
impl Combinator for CertificateRequestCombinator {
    type Result<'a> = CertificateRequest<'a>;
    type Owned = CertificateRequestOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateRequestCombinatorAlias = Mapped<(Opaque0FfCombinator, CertificateRequestExtensionsCombinator), CertificateRequestMapper>;


pub struct SpecNewSessionTicketExtensionsCombinator(SpecNewSessionTicketExtensionsCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    type SpecResult = SpecNewSessionTicketExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketExtensionsCombinatorAlias = Mapped<SpecDepend<SpecUint0FffeCombinator, SpecNewSessionTicketExtensionsExtensionsCombinator>, NewSessionTicketExtensionsMapper>;
pub struct NewSessionTicketExtensionsCont;
pub struct NewSessionTicketExtensionsCombinator(NewSessionTicketExtensionsCombinatorAlias);

impl View for NewSessionTicketExtensionsCombinator {
    type V = SpecNewSessionTicketExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketExtensionsCombinator(self.0@) }
}
impl Combinator for NewSessionTicketExtensionsCombinator {
    type Result<'a> = NewSessionTicketExtensions<'a>;
    type Owned = NewSessionTicketExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NewSessionTicketExtensionsCombinatorAlias = Mapped<Depend<Uint0FffeCombinator, NewSessionTicketExtensionsExtensionsCombinator, NewSessionTicketExtensionsCont>, NewSessionTicketExtensionsMapper>;


pub struct SpecNewSessionTicketCombinator(SpecNewSessionTicketCombinatorAlias);

impl SpecCombinator for SpecNewSessionTicketCombinator {
    type SpecResult = SpecNewSessionTicket;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecNewSessionTicketCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecNewSessionTicketCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecNewSessionTicketCombinatorAlias = Mapped<(U32Be, (U32Be, (SpecOpaque0FfCombinator, (SpecOpaque1FfffCombinator, SpecNewSessionTicketExtensionsCombinator)))), NewSessionTicketMapper>;

pub struct NewSessionTicketCombinator(NewSessionTicketCombinatorAlias);

impl View for NewSessionTicketCombinator {
    type V = SpecNewSessionTicketCombinator;
    closed spec fn view(&self) -> Self::V { SpecNewSessionTicketCombinator(self.0@) }
}
impl Combinator for NewSessionTicketCombinator {
    type Result<'a> = NewSessionTicket<'a>;
    type Owned = NewSessionTicketOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type NewSessionTicketCombinatorAlias = Mapped<(U32Be, (U32Be, (Opaque0FfCombinator, (Opaque1FfffCombinator, NewSessionTicketExtensionsCombinator)))), NewSessionTicketMapper>;


pub struct SpecCertificateVerifyCombinator(SpecCertificateVerifyCombinatorAlias);

impl SpecCombinator for SpecCertificateVerifyCombinator {
    type SpecResult = SpecCertificateVerify;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateVerifyCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateVerifyCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateVerifyCombinatorAlias = Mapped<(SpecSignatureSchemeCombinator, SpecOpaque0FfffCombinator), CertificateVerifyMapper>;

pub struct CertificateVerifyCombinator(CertificateVerifyCombinatorAlias);

impl View for CertificateVerifyCombinator {
    type V = SpecCertificateVerifyCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateVerifyCombinator(self.0@) }
}
impl Combinator for CertificateVerifyCombinator {
    type Result<'a> = CertificateVerify<'a>;
    type Owned = CertificateVerifyOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateVerifyCombinatorAlias = Mapped<(SignatureSchemeCombinator, Opaque0FfffCombinator), CertificateVerifyMapper>;


pub struct SpecContentTypeCombinator(SpecContentTypeCombinatorAlias);

impl SpecCombinator for SpecContentTypeCombinator {
    type SpecResult = SpecContentType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecContentTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecContentTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;

pub struct ContentTypeCombinator(ContentTypeCombinatorAlias);

impl View for ContentTypeCombinator {
    type V = SpecContentTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecContentTypeCombinator(self.0@) }
}
impl Combinator for ContentTypeCombinator {
    type Result<'a> = ContentType;
    type Owned = ContentTypeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ContentTypeCombinatorAlias = TryMap<U8, ContentTypeMapper>;


pub struct SpecTlsPlaintextCombinator(SpecTlsPlaintextCombinatorAlias);

impl SpecCombinator for SpecTlsPlaintextCombinator {
    type SpecResult = SpecTlsPlaintext;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTlsPlaintextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsPlaintextCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecTlsPlaintextCombinatorAlias = Mapped<(SpecContentTypeCombinator, (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator)), TlsPlaintextMapper>;

pub struct TlsPlaintextCombinator(TlsPlaintextCombinatorAlias);

impl View for TlsPlaintextCombinator {
    type V = SpecTlsPlaintextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsPlaintextCombinator(self.0@) }
}
impl Combinator for TlsPlaintextCombinator {
    type Result<'a> = TlsPlaintext<'a>;
    type Owned = TlsPlaintextOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type TlsPlaintextCombinatorAlias = Mapped<(ContentTypeCombinator, (ProtocolVersionCombinator, Opaque0FfffCombinator)), TlsPlaintextMapper>;


pub struct SpecSeverHelloExtensionExtensionDataCombinator(SpecSeverHelloExtensionExtensionDataCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    type SpecResult = SpecSeverHelloExtensionExtensionData;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverHelloExtensionExtensionDataCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionExtensionDataCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecServerNameListCombinator>, OrdChoice<Cond<SpecMaxFragmentLengthCombinator>, OrdChoice<Cond<SpecCertificateStatusRequestCombinator>, OrdChoice<Cond<SpecNamedGroupListCombinator>, OrdChoice<Cond<SpecEcPointFormatListCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecSrtpProtectionProfilesCombinator>, OrdChoice<Cond<SpecHeartbeatModeCombinator>, OrdChoice<Cond<SpecProtocolNameListCombinator>, OrdChoice<Cond<SpecSignedCertificateTimestampListCombinator>, OrdChoice<Cond<SpecClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<SpecPaddingExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecPreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSupportedVersionsClientCombinator>, OrdChoice<Cond<SpecCookieCombinator>, OrdChoice<Cond<SpecPskKeyExchangeModesCombinator>, OrdChoice<Cond<SpecCertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<SpecOidFilterExtensionCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecSignatureSchemeListCombinator>, OrdChoice<Cond<SpecKeyShareClientHelloCombinator>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>>, SeverHelloExtensionExtensionDataMapper>>;

pub struct SeverHelloExtensionExtensionDataCombinator(SeverHelloExtensionExtensionDataCombinatorAlias);

impl View for SeverHelloExtensionExtensionDataCombinator {
    type V = SpecSeverHelloExtensionExtensionDataCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionExtensionDataCombinator(self.0@) }
}
impl Combinator for SeverHelloExtensionExtensionDataCombinator {
    type Result<'a> = SeverHelloExtensionExtensionData<'a>;
    type Owned = SeverHelloExtensionExtensionDataOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SeverHelloExtensionExtensionDataCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<ServerNameListCombinator>, OrdChoice<Cond<MaxFragmentLengthCombinator>, OrdChoice<Cond<CertificateStatusRequestCombinator>, OrdChoice<Cond<NamedGroupListCombinator>, OrdChoice<Cond<EcPointFormatListCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator>, OrdChoice<Cond<SrtpProtectionProfilesCombinator>, OrdChoice<Cond<HeartbeatModeCombinator>, OrdChoice<Cond<ProtocolNameListCombinator>, OrdChoice<Cond<SignedCertificateTimestampListCombinator>, OrdChoice<Cond<ClientCertTypeClientExtensionCombinator>, OrdChoice<Cond<ServerCertTypeClientExtensionCombinator>, OrdChoice<Cond<PaddingExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<PreSharedKeyClientExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SupportedVersionsClientCombinator>, OrdChoice<Cond<CookieCombinator>, OrdChoice<Cond<PskKeyExchangeModesCombinator>, OrdChoice<Cond<CertificateAuthoritiesExtensionCombinator>, OrdChoice<Cond<OidFilterExtensionCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<SignatureSchemeListCombinator>, OrdChoice<Cond<KeyShareClientHelloCombinator>, Cond<Bytes>>>>>>>>>>>>>>>>>>>>>>>>>>>, SeverHelloExtensionExtensionDataMapper>>;


pub struct SpecSeverHelloExtensionCombinator(SpecSeverHelloExtensionCombinatorAlias);

impl SpecCombinator for SpecSeverHelloExtensionCombinator {
    type SpecResult = SpecSeverHelloExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecSeverHelloExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecSeverHelloExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecSeverHelloExtensionCombinatorAlias = Mapped<SpecDepend<(SpecExtensionTypeCombinator, U16Be), SpecSeverHelloExtensionExtensionDataCombinator>, SeverHelloExtensionMapper>;
pub struct SeverHelloExtensionCont;
pub struct SeverHelloExtensionCombinator(SeverHelloExtensionCombinatorAlias);

impl View for SeverHelloExtensionCombinator {
    type V = SpecSeverHelloExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecSeverHelloExtensionCombinator(self.0@) }
}
impl Combinator for SeverHelloExtensionCombinator {
    type Result<'a> = SeverHelloExtension<'a>;
    type Owned = SeverHelloExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type SeverHelloExtensionCombinatorAlias = Mapped<Depend<(ExtensionTypeCombinator, U16Be), SeverHelloExtensionExtensionDataCombinator, SeverHelloExtensionCont>, SeverHelloExtensionMapper>;


pub struct SpecHandshakeTypeCombinator(SpecHandshakeTypeCombinatorAlias);

impl SpecCombinator for SpecHandshakeTypeCombinator {
    type SpecResult = SpecHandshakeType;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeTypeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeTypeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeTypeCombinatorAlias = TryMap<U8, HandshakeTypeMapper>;

pub struct HandshakeTypeCombinator(HandshakeTypeCombinatorAlias);

impl View for HandshakeTypeCombinator {
    type V = SpecHandshakeTypeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeTypeCombinator(self.0@) }
}
impl Combinator for HandshakeTypeCombinator {
    type Result<'a> = HandshakeType;
    type Owned = HandshakeTypeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HandshakeTypeCombinatorAlias = TryMap<U8, HandshakeTypeMapper>;


pub struct SpecServerExtensionsExtensionsCombinator(SpecServerExtensionsExtensionsCombinatorAlias);

impl SpecCombinator for SpecServerExtensionsExtensionsCombinator {
    type SpecResult = SpecServerExtensionsExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerExtensionsExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerExtensionsExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SpecSeverHelloExtensionCombinator>>;

pub struct ServerExtensionsExtensionsCombinator(ServerExtensionsExtensionsCombinatorAlias);

impl View for ServerExtensionsExtensionsCombinator {
    type V = SpecServerExtensionsExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerExtensionsExtensionsCombinator(self.0@) }
}
impl Combinator for ServerExtensionsExtensionsCombinator {
    type Result<'a> = ServerExtensionsExtensions<'a>;
    type Owned = ServerExtensionsExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerExtensionsExtensionsCombinatorAlias = AndThen<Bytes, Repeat<SeverHelloExtensionCombinator>>;

impl SpecPred for Predicate503472032047519273 {
    type Input = u16;

    open spec fn spec_apply(&self, i: &Self::Input) -> bool {
        let i = (*i);
        if (i >= 6 && i <= 65535) {
            true
        } else {
            false
        }
    }
}

pub struct SpecServerExtensionsCombinator(SpecServerExtensionsCombinatorAlias);

impl SpecCombinator for SpecServerExtensionsCombinator {
    type SpecResult = SpecServerExtensions;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerExtensionsCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerExtensionsCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerExtensionsCombinatorAlias = Mapped<SpecDepend<Refined<U16Be, Predicate503472032047519273>, SpecServerExtensionsExtensionsCombinator>, ServerExtensionsMapper>;
pub struct Predicate503472032047519273;
impl View for Predicate503472032047519273 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}
impl Pred for Predicate503472032047519273 {
    type Input<'a> = u16;
    type InputOwned = u16;

    fn apply(&self, i: &Self::Input<'_>) -> bool {
        let i = (*i);
        if (i >= 6 && i <= 65535) {
            true
        } else {
            false
        }
    }
}
pub struct ServerExtensionsCont;
pub struct ServerExtensionsCombinator(ServerExtensionsCombinatorAlias);

impl View for ServerExtensionsCombinator {
    type V = SpecServerExtensionsCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerExtensionsCombinator(self.0@) }
}
impl Combinator for ServerExtensionsCombinator {
    type Result<'a> = ServerExtensions<'a>;
    type Owned = ServerExtensionsOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerExtensionsCombinatorAlias = Mapped<Depend<Refined<U16Be, Predicate503472032047519273>, ServerExtensionsExtensionsCombinator, ServerExtensionsCont>, ServerExtensionsMapper>;

pub const SERVERHELLO_LEGACY_COMPRESSION_METHOD: u8 = 0;

pub struct SpecServerHelloCombinator(SpecServerHelloCombinatorAlias);

impl SpecCombinator for SpecServerHelloCombinator {
    type SpecResult = SpecServerHello;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerHelloCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerHelloCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerHelloCombinatorAlias = Mapped<(SpecProtocolVersionCombinator, (SpecRandomCombinator, (SpecSessionIdCombinator, (SpecCipherSuiteCombinator, (Refined<U8, TagPred<u8>>, SpecServerExtensionsCombinator))))), ServerHelloMapper>;

pub struct ServerHelloCombinator(ServerHelloCombinatorAlias);

impl View for ServerHelloCombinator {
    type V = SpecServerHelloCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerHelloCombinator(self.0@) }
}
impl Combinator for ServerHelloCombinator {
    type Result<'a> = ServerHello<'a>;
    type Owned = ServerHelloOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerHelloCombinatorAlias = Mapped<(ProtocolVersionCombinator, (RandomCombinator, (SessionIdCombinator, (CipherSuiteCombinator, (Refined<U8, TagPred<u8>>, ServerExtensionsCombinator))))), ServerHelloMapper>;


pub struct SpecFinishedCombinator(SpecFinishedCombinatorAlias);

impl SpecCombinator for SpecFinishedCombinator {
    type SpecResult = SpecFinished;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecFinishedCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecFinishedCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecFinishedCombinatorAlias = Bytes;

pub struct FinishedCombinator(FinishedCombinatorAlias);

impl View for FinishedCombinator {
    type V = SpecFinishedCombinator;
    closed spec fn view(&self) -> Self::V { SpecFinishedCombinator(self.0@) }
}
impl Combinator for FinishedCombinator {
    type Result<'a> = Finished<'a>;
    type Owned = FinishedOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type FinishedCombinatorAlias = Bytes;


pub struct SpecHandshakeMsgCombinator(SpecHandshakeMsgCombinatorAlias);

impl SpecCombinator for SpecHandshakeMsgCombinator {
    type SpecResult = SpecHandshakeMsg;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeMsgCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeMsgCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeMsgCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<SpecClientHelloCombinator>, OrdChoice<Cond<SpecServerHelloCombinator>, OrdChoice<Cond<SpecNewSessionTicketCombinator>, OrdChoice<Cond<SpecEmptyCombinator>, OrdChoice<Cond<SpecEncryptedExtensionsCombinator>, OrdChoice<Cond<SpecCertificateCombinator>, OrdChoice<Cond<SpecCertificateRequestCombinator>, OrdChoice<Cond<SpecCertificateVerifyCombinator>, OrdChoice<Cond<SpecFinishedCombinator>, Cond<SpecKeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper>>;

pub struct HandshakeMsgCombinator(HandshakeMsgCombinatorAlias);

impl View for HandshakeMsgCombinator {
    type V = SpecHandshakeMsgCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeMsgCombinator(self.0@) }
}
impl Combinator for HandshakeMsgCombinator {
    type Result<'a> = HandshakeMsg<'a>;
    type Owned = HandshakeMsgOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HandshakeMsgCombinatorAlias = AndThen<Bytes, Mapped<OrdChoice<Cond<ClientHelloCombinator>, OrdChoice<Cond<ServerHelloCombinator>, OrdChoice<Cond<NewSessionTicketCombinator>, OrdChoice<Cond<EmptyCombinator>, OrdChoice<Cond<EncryptedExtensionsCombinator>, OrdChoice<Cond<CertificateCombinator>, OrdChoice<Cond<CertificateRequestCombinator>, OrdChoice<Cond<CertificateVerifyCombinator>, OrdChoice<Cond<FinishedCombinator>, Cond<KeyUpdateCombinator>>>>>>>>>>, HandshakeMsgMapper>>;


pub struct SpecHandshakeCombinator(SpecHandshakeCombinatorAlias);

impl SpecCombinator for SpecHandshakeCombinator {
    type SpecResult = SpecHandshake;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHandshakeCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHandshakeCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHandshakeCombinatorAlias = Mapped<SpecDepend<(SpecHandshakeTypeCombinator, U24Be), SpecHandshakeMsgCombinator>, HandshakeMapper>;
pub struct HandshakeCont;
pub struct HandshakeCombinator(HandshakeCombinatorAlias);

impl View for HandshakeCombinator {
    type V = SpecHandshakeCombinator;
    closed spec fn view(&self) -> Self::V { SpecHandshakeCombinator(self.0@) }
}
impl Combinator for HandshakeCombinator {
    type Result<'a> = Handshake<'a>;
    type Owned = HandshakeOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HandshakeCombinatorAlias = Mapped<Depend<(HandshakeTypeCombinator, U24Be), HandshakeMsgCombinator, HandshakeCont>, HandshakeMapper>;


pub struct SpecServerCertTypeServerExtensionCombinator(SpecServerCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    type SpecResult = SpecServerCertTypeServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecServerCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecServerCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecServerCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;

pub struct ServerCertTypeServerExtensionCombinator(ServerCertTypeServerExtensionCombinatorAlias);

impl View for ServerCertTypeServerExtensionCombinator {
    type V = SpecServerCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecServerCertTypeServerExtensionCombinator(self.0@) }
}
impl Combinator for ServerCertTypeServerExtensionCombinator {
    type Result<'a> = ServerCertTypeServerExtension;
    type Owned = ServerCertTypeServerExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ServerCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ServerCertTypeServerExtensionMapper>;


pub struct SpecOpaque2FfffCombinator(SpecOpaque2FfffCombinatorAlias);

impl SpecCombinator for SpecOpaque2FfffCombinator {
    type SpecResult = SpecOpaque2Ffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque2FfffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque2FfffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque2FfffCombinatorAlias = Mapped<SpecDepend<SpecUint2FfffCombinator, Bytes>, Opaque2FfffMapper>;
pub struct Opaque2FfffCont;
pub struct Opaque2FfffCombinator(Opaque2FfffCombinatorAlias);

impl View for Opaque2FfffCombinator {
    type V = SpecOpaque2FfffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque2FfffCombinator(self.0@) }
}
impl Combinator for Opaque2FfffCombinator {
    type Result<'a> = Opaque2Ffff<'a>;
    type Owned = Opaque2FfffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque2FfffCombinatorAlias = Mapped<Depend<Uint2FfffCombinator, Bytes, Opaque2FfffCont>, Opaque2FfffMapper>;


pub struct SpecOcspResponseCombinator(SpecOcspResponseCombinatorAlias);

impl SpecCombinator for SpecOcspResponseCombinator {
    type SpecResult = SpecOcspResponse;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOcspResponseCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOcspResponseCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOcspResponseCombinatorAlias = SpecOpaque1FfffffCombinator;

pub struct OcspResponseCombinator(OcspResponseCombinatorAlias);

impl View for OcspResponseCombinator {
    type V = SpecOcspResponseCombinator;
    closed spec fn view(&self) -> Self::V { SpecOcspResponseCombinator(self.0@) }
}
impl Combinator for OcspResponseCombinator {
    type Result<'a> = OcspResponse<'a>;
    type Owned = OcspResponseOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type OcspResponseCombinatorAlias = Opaque1FfffffCombinator;

pub const CERTIFICATESTATUS_STATUS_TYPE: u8 = 1;

pub struct SpecCertificateStatusCombinator(SpecCertificateStatusCombinatorAlias);

impl SpecCombinator for SpecCertificateStatusCombinator {
    type SpecResult = SpecCertificateStatus;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecCertificateStatusCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecCertificateStatusCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecCertificateStatusCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, SpecOcspResponseCombinator), CertificateStatusMapper>;

pub struct CertificateStatusCombinator(CertificateStatusCombinatorAlias);

impl View for CertificateStatusCombinator {
    type V = SpecCertificateStatusCombinator;
    closed spec fn view(&self) -> Self::V { SpecCertificateStatusCombinator(self.0@) }
}
impl Combinator for CertificateStatusCombinator {
    type Result<'a> = CertificateStatus<'a>;
    type Owned = CertificateStatusOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type CertificateStatusCombinatorAlias = Mapped<(Refined<U8, TagPred<u8>>, OcspResponseCombinator), CertificateStatusMapper>;


pub struct SpecHeartbeatExtensionCombinator(SpecHeartbeatExtensionCombinatorAlias);

impl SpecCombinator for SpecHeartbeatExtensionCombinator {
    type SpecResult = SpecHeartbeatExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecHeartbeatExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecHeartbeatExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecHeartbeatExtensionCombinatorAlias = Mapped<SpecHeartbeatModeCombinator, HeartbeatExtensionMapper>;

pub struct HeartbeatExtensionCombinator(HeartbeatExtensionCombinatorAlias);

impl View for HeartbeatExtensionCombinator {
    type V = SpecHeartbeatExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecHeartbeatExtensionCombinator(self.0@) }
}
impl Combinator for HeartbeatExtensionCombinator {
    type Result<'a> = HeartbeatExtension;
    type Owned = HeartbeatExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type HeartbeatExtensionCombinatorAlias = Mapped<HeartbeatModeCombinator, HeartbeatExtensionMapper>;


pub struct SpecAlertLevelCombinator(SpecAlertLevelCombinatorAlias);

impl SpecCombinator for SpecAlertLevelCombinator {
    type SpecResult = SpecAlertLevel;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertLevelCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertLevelCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;

pub struct AlertLevelCombinator(AlertLevelCombinatorAlias);

impl View for AlertLevelCombinator {
    type V = SpecAlertLevelCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertLevelCombinator(self.0@) }
}
impl Combinator for AlertLevelCombinator {
    type Result<'a> = AlertLevel;
    type Owned = AlertLevelOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type AlertLevelCombinatorAlias = TryMap<U8, AlertLevelMapper>;


pub struct SpecUnknownExtensionCombinator(SpecUnknownExtensionCombinatorAlias);

impl SpecCombinator for SpecUnknownExtensionCombinator {
    type SpecResult = SpecUnknownExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecUnknownExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecUnknownExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecUnknownExtensionCombinatorAlias = SpecOpaque0FfffCombinator;

pub struct UnknownExtensionCombinator(UnknownExtensionCombinatorAlias);

impl View for UnknownExtensionCombinator {
    type V = SpecUnknownExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecUnknownExtensionCombinator(self.0@) }
}
impl Combinator for UnknownExtensionCombinator {
    type Result<'a> = UnknownExtension<'a>;
    type Owned = UnknownExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type UnknownExtensionCombinatorAlias = Opaque0FfffCombinator;


pub struct SpecAlertDescriptionCombinator(SpecAlertDescriptionCombinatorAlias);

impl SpecCombinator for SpecAlertDescriptionCombinator {
    type SpecResult = SpecAlertDescription;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertDescriptionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertDescriptionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertDescriptionCombinatorAlias = TryMap<U8, AlertDescriptionMapper>;

pub struct AlertDescriptionCombinator(AlertDescriptionCombinatorAlias);

impl View for AlertDescriptionCombinator {
    type V = SpecAlertDescriptionCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertDescriptionCombinator(self.0@) }
}
impl Combinator for AlertDescriptionCombinator {
    type Result<'a> = AlertDescription;
    type Owned = AlertDescriptionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type AlertDescriptionCombinatorAlias = TryMap<U8, AlertDescriptionMapper>;


pub struct SpecAlertCombinator(SpecAlertCombinatorAlias);

impl SpecCombinator for SpecAlertCombinator {
    type SpecResult = SpecAlert;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecAlertCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecAlertCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecAlertCombinatorAlias = Mapped<(SpecAlertLevelCombinator, SpecAlertDescriptionCombinator), AlertMapper>;

pub struct AlertCombinator(AlertCombinatorAlias);

impl View for AlertCombinator {
    type V = SpecAlertCombinator;
    closed spec fn view(&self) -> Self::V { SpecAlertCombinator(self.0@) }
}
impl Combinator for AlertCombinator {
    type Result<'a> = Alert;
    type Owned = AlertOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type AlertCombinatorAlias = Mapped<(AlertLevelCombinator, AlertDescriptionCombinator), AlertMapper>;


pub struct SpecClientCertTypeServerExtensionCombinator(SpecClientCertTypeServerExtensionCombinatorAlias);

impl SpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    type SpecResult = SpecClientCertTypeServerExtension;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecClientCertTypeServerExtensionCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecClientCertTypeServerExtensionCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecClientCertTypeServerExtensionCombinatorAlias = Mapped<SpecCertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;

pub struct ClientCertTypeServerExtensionCombinator(ClientCertTypeServerExtensionCombinatorAlias);

impl View for ClientCertTypeServerExtensionCombinator {
    type V = SpecClientCertTypeServerExtensionCombinator;
    closed spec fn view(&self) -> Self::V { SpecClientCertTypeServerExtensionCombinator(self.0@) }
}
impl Combinator for ClientCertTypeServerExtensionCombinator {
    type Result<'a> = ClientCertTypeServerExtension;
    type Owned = ClientCertTypeServerExtensionOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type ClientCertTypeServerExtensionCombinatorAlias = Mapped<CertificateTypeCombinator, ClientCertTypeServerExtensionMapper>;


pub struct SpecTlsCiphertextCombinator(SpecTlsCiphertextCombinatorAlias);

impl SpecCombinator for SpecTlsCiphertextCombinator {
    type SpecResult = SpecTlsCiphertext;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecTlsCiphertextCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecTlsCiphertextCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecTlsCiphertextCombinatorAlias = Mapped<(SpecContentTypeCombinator, (SpecProtocolVersionCombinator, SpecOpaque0FfffCombinator)), TlsCiphertextMapper>;

pub struct TlsCiphertextCombinator(TlsCiphertextCombinatorAlias);

impl View for TlsCiphertextCombinator {
    type V = SpecTlsCiphertextCombinator;
    closed spec fn view(&self) -> Self::V { SpecTlsCiphertextCombinator(self.0@) }
}
impl Combinator for TlsCiphertextCombinator {
    type Result<'a> = TlsCiphertext<'a>;
    type Owned = TlsCiphertextOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type TlsCiphertextCombinatorAlias = Mapped<(ContentTypeCombinator, (ProtocolVersionCombinator, Opaque0FfffCombinator)), TlsCiphertextMapper>;


pub struct SpecOpaque0FfffffCombinator(SpecOpaque0FfffffCombinatorAlias);

impl SpecCombinator for SpecOpaque0FfffffCombinator {
    type SpecResult = SpecOpaque0Ffffff;
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> 
    { self.0.spec_parse(s) }
    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> 
    { self.0.spec_serialize(v) }
    proof fn spec_parse_wf(&self, s: Seq<u8>)
    { self.0.spec_parse_wf(s) }

}
impl SecureSpecCombinator for SpecOpaque0FfffffCombinator {
    open spec fn is_prefix_secure() -> bool 
    { SpecOpaque0FfffffCombinatorAlias::is_prefix_secure() }
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
    { self.0.theorem_serialize_parse_roundtrip(v) }
    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
    { self.0.theorem_parse_serialize_roundtrip(buf) }
    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>)
    { self.0.lemma_prefix_secure(s1, s2) }
}
pub type SpecOpaque0FfffffCombinatorAlias = Mapped<SpecDepend<U24Be, Bytes>, Opaque0FfffffMapper>;
pub struct Opaque0FfffffCont;
pub struct Opaque0FfffffCombinator(Opaque0FfffffCombinatorAlias);

impl View for Opaque0FfffffCombinator {
    type V = SpecOpaque0FfffffCombinator;
    closed spec fn view(&self) -> Self::V { SpecOpaque0FfffffCombinator(self.0@) }
}
impl Combinator for Opaque0FfffffCombinator {
    type Result<'a> = Opaque0Ffffff<'a>;
    type Owned = Opaque0FfffffOwned;
    closed spec fn spec_length(&self) -> Option<usize> 
    { self.0.spec_length() }
    fn length(&self) -> Option<usize> 
    { self.0.length() }
    closed spec fn parse_requires(&self) -> bool 
    { self.0.parse_requires() }
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) 
    { self.0.parse(s) }
    closed spec fn serialize_requires(&self) -> bool 
    { self.0.serialize_requires() }
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (o: Result<usize, SerializeError>)
    { self.0.serialize(v, data, pos) }
} 
pub type Opaque0FfffffCombinatorAlias = Mapped<Depend<U24Be, Bytes, Opaque0FfffffCont>, Opaque0FfffffMapper>;


pub closed spec fn spec_extension_type() -> SpecExtensionTypeCombinator {
    SpecExtensionTypeCombinator(U16Be)
}
 
pub fn extension_type() -> (o: ExtensionTypeCombinator)
    ensures o@ == spec_extension_type(),
{
    ExtensionTypeCombinator(U16Be)
}
 

pub closed spec fn spec_uint_0_ffff() -> SpecUint0FfffCombinator {
    SpecUint0FfffCombinator(U16Be)
}
 
pub fn uint_0_ffff() -> (o: Uint0FfffCombinator)
    ensures o@ == spec_uint_0_ffff(),
{
    Uint0FfffCombinator(U16Be)
}
 

pub closed spec fn spec_opaque_0_ffff() -> SpecOpaque0FfffCombinator {
    SpecOpaque0FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_opaque0_ffff_cont(deps),
        },
        mapper: Opaque0FfffMapper,
    }
)
}

pub open spec fn spec_opaque0_ffff_cont(deps: SpecUint0Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_0_ffff() -> (o: Opaque0FfffCombinator)
    ensures o@ == spec_opaque_0_ffff(),
{
    Opaque0FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: Opaque0FfffCont,
            spec_snd: Ghost(|deps| spec_opaque0_ffff_cont(deps)),
        },
        mapper: Opaque0FfffMapper,
    }
)
}

impl Continuation<Uint0Ffff> for Opaque0FfffCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_extension() -> SpecExtensionCombinator {
    SpecExtensionCombinator(Mapped { inner: (spec_extension_type(), spec_opaque_0_ffff()), mapper: ExtensionMapper })
}
 
pub fn extension() -> (o: ExtensionCombinator)
    ensures o@ == spec_extension(),
{
    ExtensionCombinator(Mapped { inner: (extension_type(), opaque_0_ffff()), mapper: ExtensionMapper })
}
 

pub closed spec fn spec_new_session_ticket_extensions_extensions(l: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    SpecNewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}
 
pub fn new_session_ticket_extensions_extensions<'a>(l: Uint0Fffe) -> (o: NewSessionTicketExtensionsExtensionsCombinator)
    ensures o@ == spec_new_session_ticket_extensions_extensions(l@),
{
    NewSessionTicketExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
}
 

pub closed spec fn spec_protocol_version() -> SpecProtocolVersionCombinator {
    SpecProtocolVersionCombinator(U16Be)
}
 
pub fn protocol_version() -> (o: ProtocolVersionCombinator)
    ensures o@ == spec_protocol_version(),
{
    ProtocolVersionCombinator(U16Be)
}
 

pub closed spec fn spec_supported_versions_client_versions(l: u8) -> SpecSupportedVersionsClientVersionsCombinator {
    SpecSupportedVersionsClientVersionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_protocol_version())))
}
 
pub fn supported_versions_client_versions(l: u8) -> (o: SupportedVersionsClientVersionsCombinator)
    ensures o@ == spec_supported_versions_client_versions(l@),
{
    SupportedVersionsClientVersionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(protocol_version())))
}
 

pub closed spec fn spec_ec_point_format() -> SpecEcPointFormatCombinator {
    SpecEcPointFormatCombinator(U8)
}
 
pub fn ec_point_format() -> (o: EcPointFormatCombinator)
    ensures o@ == spec_ec_point_format(),
{
    EcPointFormatCombinator(U8)
}
 

pub closed spec fn spec_ec_point_format_list_list(l: SpecUint1Ff) -> SpecEcPointFormatListListCombinator {
    SpecEcPointFormatListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_ec_point_format())))
}
 
pub fn ec_point_format_list_list(l: Uint1Ff) -> (o: EcPointFormatListListCombinator)
    ensures o@ == spec_ec_point_format_list_list(l@),
{
    EcPointFormatListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(ec_point_format())))
}
 

pub closed spec fn spec_zero_byte() -> SpecZeroByteCombinator {
    SpecZeroByteCombinator(Mapped { inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) }, mapper: ZeroByteMapper })
}
 
pub fn zero_byte() -> (o: ZeroByteCombinator)
    ensures o@ == spec_zero_byte(),
{
    ZeroByteCombinator(Mapped { inner: Refined { inner: U8, predicate: TagPred(ZEROBYTE_ZERO) }, mapper: ZeroByteMapper })
}
 

pub closed spec fn spec_padding_extension_padding(l: SpecUint0Ffff) -> SpecPaddingExtensionPaddingCombinator {
    SpecPaddingExtensionPaddingCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_zero_byte())))
}
 
pub fn padding_extension_padding(l: Uint0Ffff) -> (o: PaddingExtensionPaddingCombinator)
    ensures o@ == spec_padding_extension_padding(l@),
{
    PaddingExtensionPaddingCombinator(AndThen(Bytes(l.ex_into()), Repeat(zero_byte())))
}
 

pub closed spec fn spec_psk_key_exchange_mode() -> SpecPskKeyExchangeModeCombinator {
    SpecPskKeyExchangeModeCombinator(U8)
}
 
pub fn psk_key_exchange_mode() -> (o: PskKeyExchangeModeCombinator)
    ensures o@ == spec_psk_key_exchange_mode(),
{
    PskKeyExchangeModeCombinator(U8)
}
 

pub closed spec fn spec_psk_key_exchange_modes_modes(l: SpecUint1Ff) -> SpecPskKeyExchangeModesModesCombinator {
    SpecPskKeyExchangeModesModesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_key_exchange_mode())))
}
 
pub fn psk_key_exchange_modes_modes(l: Uint1Ff) -> (o: PskKeyExchangeModesModesCombinator)
    ensures o@ == spec_psk_key_exchange_modes_modes(l@),
{
    PskKeyExchangeModesModesCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_key_exchange_mode())))
}
 

pub closed spec fn spec_uint_1_ffff() -> SpecUint1FfffCombinator {
    SpecUint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate11955646336730306823 })
}
 
pub fn uint_1_ffff() -> (o: Uint1FfffCombinator)
    ensures o@ == spec_uint_1_ffff(),
{
    Uint1FfffCombinator(Refined { inner: U16Be, predicate: Predicate11955646336730306823 })
}
 

pub closed spec fn spec_name_type() -> SpecNameTypeCombinator {
    SpecNameTypeCombinator(U8)
}
 
pub fn name_type() -> (o: NameTypeCombinator)
    ensures o@ == spec_name_type(),
{
    NameTypeCombinator(U8)
}
 

pub closed spec fn spec_opaque_1_ffff() -> SpecOpaque1FfffCombinator {
    SpecOpaque1FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_opaque1_ffff_cont(deps),
        },
        mapper: Opaque1FfffMapper,
    }
)
}

pub open spec fn spec_opaque1_ffff_cont(deps: SpecUint1Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_1_ffff() -> (o: Opaque1FfffCombinator)
    ensures o@ == spec_opaque_1_ffff(),
{
    Opaque1FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: Opaque1FfffCont,
            spec_snd: Ghost(|deps| spec_opaque1_ffff_cont(deps)),
        },
        mapper: Opaque1FfffMapper,
    }
)
}

impl Continuation<Uint1Ffff> for Opaque1FfffCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_host_name() -> SpecHostNameCombinator {
    SpecHostNameCombinator(spec_opaque_1_ffff())
}
 
pub fn host_name() -> (o: HostNameCombinator)
    ensures o@ == spec_host_name(),
{
    HostNameCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_unknown_name() -> SpecUnknownNameCombinator {
    SpecUnknownNameCombinator(spec_opaque_1_ffff())
}
 
pub fn unknown_name() -> (o: UnknownNameCombinator)
    ensures o@ == spec_unknown_name(),
{
    UnknownNameCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_server_name_name(name_type: SpecNameType) -> SpecServerNameNameCombinator {
    SpecServerNameNameCombinator(Mapped { inner: OrdChoice(Cond { cond: name_type == 0, inner: spec_host_name() }, Cond { cond: !(name_type == 0), inner: spec_unknown_name() }), mapper: ServerNameNameMapper })
}
 
pub fn server_name_name<'a>(name_type: NameType) -> (o: ServerNameNameCombinator)
    ensures o@ == spec_server_name_name(name_type@),
{
    ServerNameNameCombinator(Mapped { inner: OrdChoice(Cond { cond: name_type == 0, inner: host_name() }, Cond { cond: !(name_type == 0), inner: unknown_name() }), mapper: ServerNameNameMapper })
}
 

pub closed spec fn spec_server_name() -> SpecServerNameCombinator {
    SpecServerNameCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_name_type(),
            snd: |deps| spec_server_name_cont(deps),
        },
        mapper: ServerNameMapper,
    }
)
}

pub open spec fn spec_server_name_cont(deps: SpecNameType) -> SpecServerNameNameCombinator {
    let name_type = deps;
    spec_server_name_name(name_type)
}
 
pub fn server_name() -> (o: ServerNameCombinator)
    ensures o@ == spec_server_name(),
{
    ServerNameCombinator(
    Mapped {
        inner: Depend {
            fst: name_type(),
            snd: ServerNameCont,
            spec_snd: Ghost(|deps| spec_server_name_cont(deps)),
        },
        mapper: ServerNameMapper,
    }
)
}

impl Continuation<NameType> for ServerNameCont {
    type Output = ServerNameNameCombinator;

    open spec fn requires(&self, deps: NameType) -> bool {
        true
    }

    open spec fn ensures(&self, deps: NameType, o: Self::Output) -> bool {
        o@ == spec_server_name_cont(deps@)
    }

    fn apply(&self, deps: NameType) -> Self::Output {
        let name_type = deps;
        server_name_name(name_type)
    }
}
 

pub closed spec fn spec_server_name_list_list(l: SpecUint1Ffff) -> SpecServerNameListListCombinator {
    SpecServerNameListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_server_name())))
}
 
pub fn server_name_list_list<'a>(l: Uint1Ffff) -> (o: ServerNameListListCombinator)
    ensures o@ == spec_server_name_list_list(l@),
{
    ServerNameListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(server_name())))
}
 

pub closed spec fn spec_server_name_list() -> SpecServerNameListCombinator {
    SpecServerNameListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_server_name_list_cont(deps),
        },
        mapper: ServerNameListMapper,
    }
)
}

pub open spec fn spec_server_name_list_cont(deps: SpecUint1Ffff) -> SpecServerNameListListCombinator {
    let l = deps;
    spec_server_name_list_list(l)
}
 
pub fn server_name_list() -> (o: ServerNameListCombinator)
    ensures o@ == spec_server_name_list(),
{
    ServerNameListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: ServerNameListCont,
            spec_snd: Ghost(|deps| spec_server_name_list_cont(deps)),
        },
        mapper: ServerNameListMapper,
    }
)
}

impl Continuation<Uint1Ffff> for ServerNameListCont {
    type Output = ServerNameListListCombinator;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_server_name_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        server_name_list_list(l)
    }
}
 

pub closed spec fn spec_max_fragment_length() -> SpecMaxFragmentLengthCombinator {
    SpecMaxFragmentLengthCombinator(U8)
}
 
pub fn max_fragment_length() -> (o: MaxFragmentLengthCombinator)
    ensures o@ == spec_max_fragment_length(),
{
    MaxFragmentLengthCombinator(U8)
}
 

pub closed spec fn spec_responder_id() -> SpecResponderIdCombinator {
    SpecResponderIdCombinator(spec_opaque_1_ffff())
}
 
pub fn responder_id() -> (o: ResponderIdCombinator)
    ensures o@ == spec_responder_id(),
{
    ResponderIdCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_responder_id_list_list(l: SpecUint0Ffff) -> SpecResponderIdListListCombinator {
    SpecResponderIdListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_responder_id())))
}
 
pub fn responder_id_list_list<'a>(l: Uint0Ffff) -> (o: ResponderIdListListCombinator)
    ensures o@ == spec_responder_id_list_list(l@),
{
    ResponderIdListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(responder_id())))
}
 

pub closed spec fn spec_responder_id_list() -> SpecResponderIdListCombinator {
    SpecResponderIdListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_responder_id_list_cont(deps),
        },
        mapper: ResponderIdListMapper,
    }
)
}

pub open spec fn spec_responder_id_list_cont(deps: SpecUint0Ffff) -> SpecResponderIdListListCombinator {
    let l = deps;
    spec_responder_id_list_list(l)
}
 
pub fn responder_id_list() -> (o: ResponderIdListCombinator)
    ensures o@ == spec_responder_id_list(),
{
    ResponderIdListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: ResponderIdListCont,
            spec_snd: Ghost(|deps| spec_responder_id_list_cont(deps)),
        },
        mapper: ResponderIdListMapper,
    }
)
}

impl Continuation<Uint0Ffff> for ResponderIdListCont {
    type Output = ResponderIdListListCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_responder_id_list_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        responder_id_list_list(l)
    }
}
 

pub closed spec fn spec_ocsp_extensions() -> SpecOcspExtensionsCombinator {
    SpecOcspExtensionsCombinator(spec_opaque_0_ffff())
}
 
pub fn ocsp_extensions() -> (o: OcspExtensionsCombinator)
    ensures o@ == spec_ocsp_extensions(),
{
    OcspExtensionsCombinator(opaque_0_ffff())
}
 

pub closed spec fn spec_oscp_status_request() -> SpecOscpStatusRequestCombinator {
    SpecOscpStatusRequestCombinator(Mapped { inner: (spec_responder_id_list(), spec_ocsp_extensions()), mapper: OscpStatusRequestMapper })
}
 
pub fn oscp_status_request() -> (o: OscpStatusRequestCombinator)
    ensures o@ == spec_oscp_status_request(),
{
    OscpStatusRequestCombinator(Mapped { inner: (responder_id_list(), ocsp_extensions()), mapper: OscpStatusRequestMapper })
}
 

pub closed spec fn spec_certificate_status_request() -> SpecCertificateStatusRequestCombinator {
    SpecCertificateStatusRequestCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, spec_oscp_status_request()), mapper: CertificateStatusRequestMapper })
}
 
pub fn certificate_status_request() -> (o: CertificateStatusRequestCombinator)
    ensures o@ == spec_certificate_status_request(),
{
    CertificateStatusRequestCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUSREQUEST_STATUS_TYPE) }, oscp_status_request()), mapper: CertificateStatusRequestMapper })
}
 

pub closed spec fn spec_uint_2_ffff() -> SpecUint2FfffCombinator {
    SpecUint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate5950696943328973166 })
}
 
pub fn uint_2_ffff() -> (o: Uint2FfffCombinator)
    ensures o@ == spec_uint_2_ffff(),
{
    Uint2FfffCombinator(Refined { inner: U16Be, predicate: Predicate5950696943328973166 })
}
 

pub closed spec fn spec_named_group() -> SpecNamedGroupCombinator {
    SpecNamedGroupCombinator(U16Be)
}
 
pub fn named_group() -> (o: NamedGroupCombinator)
    ensures o@ == spec_named_group(),
{
    NamedGroupCombinator(U16Be)
}
 

pub closed spec fn spec_named_group_list_list(l: SpecUint2Ffff) -> SpecNamedGroupListListCombinator {
    SpecNamedGroupListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_named_group())))
}
 
pub fn named_group_list_list(l: Uint2Ffff) -> (o: NamedGroupListListCombinator)
    ensures o@ == spec_named_group_list_list(l@),
{
    NamedGroupListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(named_group())))
}
 

pub closed spec fn spec_named_group_list() -> SpecNamedGroupListCombinator {
    SpecNamedGroupListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_named_group_list_cont(deps),
        },
        mapper: NamedGroupListMapper,
    }
)
}

pub open spec fn spec_named_group_list_cont(deps: SpecUint2Ffff) -> SpecNamedGroupListListCombinator {
    let l = deps;
    spec_named_group_list_list(l)
}
 
pub fn named_group_list() -> (o: NamedGroupListCombinator)
    ensures o@ == spec_named_group_list(),
{
    NamedGroupListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: NamedGroupListCont,
            spec_snd: Ghost(|deps| spec_named_group_list_cont(deps)),
        },
        mapper: NamedGroupListMapper,
    }
)
}

impl Continuation<Uint2Ffff> for NamedGroupListCont {
    type Output = NamedGroupListListCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_named_group_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        named_group_list_list(l)
    }
}
 

pub closed spec fn spec_uint_1_ff() -> SpecUint1FfCombinator {
    SpecUint1FfCombinator(Refined { inner: U8, predicate: Predicate13930216038658429813 })
}
 
pub fn uint_1_ff() -> (o: Uint1FfCombinator)
    ensures o@ == spec_uint_1_ff(),
{
    Uint1FfCombinator(Refined { inner: U8, predicate: Predicate13930216038658429813 })
}
 

pub closed spec fn spec_ec_point_format_list() -> SpecEcPointFormatListCombinator {
    SpecEcPointFormatListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_ec_point_format_list_cont(deps),
        },
        mapper: EcPointFormatListMapper,
    }
)
}

pub open spec fn spec_ec_point_format_list_cont(deps: SpecUint1Ff) -> SpecEcPointFormatListListCombinator {
    let l = deps;
    spec_ec_point_format_list_list(l)
}
 
pub fn ec_point_format_list() -> (o: EcPointFormatListCombinator)
    ensures o@ == spec_ec_point_format_list(),
{
    EcPointFormatListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: EcPointFormatListCont,
            spec_snd: Ghost(|deps| spec_ec_point_format_list_cont(deps)),
        },
        mapper: EcPointFormatListMapper,
    }
)
}

impl Continuation<Uint1Ff> for EcPointFormatListCont {
    type Output = EcPointFormatListListCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_ec_point_format_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        ec_point_format_list_list(l)
    }
}
 

pub closed spec fn spec_uint_2_fffe() -> SpecUint2FffeCombinator {
    SpecUint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate13238841935489611399 })
}
 
pub fn uint_2_fffe() -> (o: Uint2FffeCombinator)
    ensures o@ == spec_uint_2_fffe(),
{
    Uint2FffeCombinator(Refined { inner: U16Be, predicate: Predicate13238841935489611399 })
}
 

pub closed spec fn spec_signature_scheme() -> SpecSignatureSchemeCombinator {
    SpecSignatureSchemeCombinator(U16Be)
}
 
pub fn signature_scheme() -> (o: SignatureSchemeCombinator)
    ensures o@ == spec_signature_scheme(),
{
    SignatureSchemeCombinator(U16Be)
}
 

pub closed spec fn spec_signature_scheme_list_list(l: SpecUint2Fffe) -> SpecSignatureSchemeListListCombinator {
    SpecSignatureSchemeListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_signature_scheme())))
}
 
pub fn signature_scheme_list_list(l: Uint2Fffe) -> (o: SignatureSchemeListListCombinator)
    ensures o@ == spec_signature_scheme_list_list(l@),
{
    SignatureSchemeListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(signature_scheme())))
}
 

pub closed spec fn spec_signature_scheme_list() -> SpecSignatureSchemeListCombinator {
    SpecSignatureSchemeListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_fffe(),
            snd: |deps| spec_signature_scheme_list_cont(deps),
        },
        mapper: SignatureSchemeListMapper,
    }
)
}

pub open spec fn spec_signature_scheme_list_cont(deps: SpecUint2Fffe) -> SpecSignatureSchemeListListCombinator {
    let l = deps;
    spec_signature_scheme_list_list(l)
}
 
pub fn signature_scheme_list() -> (o: SignatureSchemeListCombinator)
    ensures o@ == spec_signature_scheme_list(),
{
    SignatureSchemeListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_fffe(),
            snd: SignatureSchemeListCont,
            spec_snd: Ghost(|deps| spec_signature_scheme_list_cont(deps)),
        },
        mapper: SignatureSchemeListMapper,
    }
)
}

impl Continuation<Uint2Fffe> for SignatureSchemeListCont {
    type Output = SignatureSchemeListListCombinator;

    open spec fn requires(&self, deps: Uint2Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_signature_scheme_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Fffe) -> Self::Output {
        let l = deps;
        signature_scheme_list_list(l)
    }
}
 

pub closed spec fn spec_srtp_protection_profile() -> SpecSrtpProtectionProfileCombinator {
    SpecSrtpProtectionProfileCombinator(BytesN::<2>)
}
 
pub fn srtp_protection_profile() -> (o: SrtpProtectionProfileCombinator)
    ensures o@ == spec_srtp_protection_profile(),
{
    SrtpProtectionProfileCombinator(BytesN::<2>)
}
 

pub closed spec fn spec_srtp_protection_profiles_list(l: SpecUint2Ffff) -> SpecSrtpProtectionProfilesListCombinator {
    SpecSrtpProtectionProfilesListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_srtp_protection_profile())))
}
 
pub fn srtp_protection_profiles_list<'a>(l: Uint2Ffff) -> (o: SrtpProtectionProfilesListCombinator)
    ensures o@ == spec_srtp_protection_profiles_list(l@),
{
    SrtpProtectionProfilesListCombinator(AndThen(Bytes(l.ex_into()), Repeat(srtp_protection_profile())))
}
 

pub closed spec fn spec_srtp_protection_profiles() -> SpecSrtpProtectionProfilesCombinator {
    SpecSrtpProtectionProfilesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_srtp_protection_profiles_cont(deps),
        },
        mapper: SrtpProtectionProfilesMapper,
    }
)
}

pub open spec fn spec_srtp_protection_profiles_cont(deps: SpecUint2Ffff) -> SpecSrtpProtectionProfilesListCombinator {
    let l = deps;
    spec_srtp_protection_profiles_list(l)
}
 
pub fn srtp_protection_profiles() -> (o: SrtpProtectionProfilesCombinator)
    ensures o@ == spec_srtp_protection_profiles(),
{
    SrtpProtectionProfilesCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: SrtpProtectionProfilesCont,
            spec_snd: Ghost(|deps| spec_srtp_protection_profiles_cont(deps)),
        },
        mapper: SrtpProtectionProfilesMapper,
    }
)
}

impl Continuation<Uint2Ffff> for SrtpProtectionProfilesCont {
    type Output = SrtpProtectionProfilesListCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_srtp_protection_profiles_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        srtp_protection_profiles_list(l)
    }
}
 

pub closed spec fn spec_uint_0_ff() -> SpecUint0FfCombinator {
    SpecUint0FfCombinator(U8)
}
 
pub fn uint_0_ff() -> (o: Uint0FfCombinator)
    ensures o@ == spec_uint_0_ff(),
{
    Uint0FfCombinator(U8)
}
 

pub closed spec fn spec_opaque_0_ff() -> SpecOpaque0FfCombinator {
    SpecOpaque0FfCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ff(),
            snd: |deps| spec_opaque0_ff_cont(deps),
        },
        mapper: Opaque0FfMapper,
    }
)
}

pub open spec fn spec_opaque0_ff_cont(deps: SpecUint0Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_0_ff() -> (o: Opaque0FfCombinator)
    ensures o@ == spec_opaque_0_ff(),
{
    Opaque0FfCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ff(),
            snd: Opaque0FfCont,
            spec_snd: Ghost(|deps| spec_opaque0_ff_cont(deps)),
        },
        mapper: Opaque0FfMapper,
    }
)
}

impl Continuation<Uint0Ff> for Opaque0FfCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint0Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ff, o: Self::Output) -> bool {
        o@ == spec_opaque0_ff_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_use_srtp_data() -> SpecUseSrtpDataCombinator {
    SpecUseSrtpDataCombinator(Mapped { inner: (spec_srtp_protection_profiles(), spec_opaque_0_ff()), mapper: UseSrtpDataMapper })
}
 
pub fn use_srtp_data() -> (o: UseSrtpDataCombinator)
    ensures o@ == spec_use_srtp_data(),
{
    UseSrtpDataCombinator(Mapped { inner: (srtp_protection_profiles(), opaque_0_ff()), mapper: UseSrtpDataMapper })
}
 

pub closed spec fn spec_heartbeat_mode() -> SpecHeartbeatModeCombinator {
    SpecHeartbeatModeCombinator(U8)
}
 
pub fn heartbeat_mode() -> (o: HeartbeatModeCombinator)
    ensures o@ == spec_heartbeat_mode(),
{
    HeartbeatModeCombinator(U8)
}
 

pub closed spec fn spec_opaque_1_ff() -> SpecOpaque1FfCombinator {
    SpecOpaque1FfCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_opaque1_ff_cont(deps),
        },
        mapper: Opaque1FfMapper,
    }
)
}

pub open spec fn spec_opaque1_ff_cont(deps: SpecUint1Ff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_1_ff() -> (o: Opaque1FfCombinator)
    ensures o@ == spec_opaque_1_ff(),
{
    Opaque1FfCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: Opaque1FfCont,
            spec_snd: Ghost(|deps| spec_opaque1_ff_cont(deps)),
        },
        mapper: Opaque1FfMapper,
    }
)
}

impl Continuation<Uint1Ff> for Opaque1FfCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_opaque1_ff_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_protocol_name() -> SpecProtocolNameCombinator {
    SpecProtocolNameCombinator(spec_opaque_1_ff())
}
 
pub fn protocol_name() -> (o: ProtocolNameCombinator)
    ensures o@ == spec_protocol_name(),
{
    ProtocolNameCombinator(opaque_1_ff())
}
 

pub closed spec fn spec_protocol_name_list_list(l: SpecUint2Ffff) -> SpecProtocolNameListListCombinator {
    SpecProtocolNameListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_protocol_name())))
}
 
pub fn protocol_name_list_list<'a>(l: Uint2Ffff) -> (o: ProtocolNameListListCombinator)
    ensures o@ == spec_protocol_name_list_list(l@),
{
    ProtocolNameListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(protocol_name())))
}
 

pub closed spec fn spec_protocol_name_list() -> SpecProtocolNameListCombinator {
    SpecProtocolNameListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_protocol_name_list_cont(deps),
        },
        mapper: ProtocolNameListMapper,
    }
)
}

pub open spec fn spec_protocol_name_list_cont(deps: SpecUint2Ffff) -> SpecProtocolNameListListCombinator {
    let l = deps;
    spec_protocol_name_list_list(l)
}
 
pub fn protocol_name_list() -> (o: ProtocolNameListCombinator)
    ensures o@ == spec_protocol_name_list(),
{
    ProtocolNameListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: ProtocolNameListCont,
            spec_snd: Ghost(|deps| spec_protocol_name_list_cont(deps)),
        },
        mapper: ProtocolNameListMapper,
    }
)
}

impl Continuation<Uint2Ffff> for ProtocolNameListCont {
    type Output = ProtocolNameListListCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_protocol_name_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        protocol_name_list_list(l)
    }
}
 

pub closed spec fn spec_serialized_sct() -> SpecSerializedSctCombinator {
    SpecSerializedSctCombinator(spec_opaque_1_ffff())
}
 
pub fn serialized_sct() -> (o: SerializedSctCombinator)
    ensures o@ == spec_serialized_sct(),
{
    SerializedSctCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_signed_certificate_timestamp_list_list(l: SpecUint1Ffff) -> SpecSignedCertificateTimestampListListCombinator {
    SpecSignedCertificateTimestampListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_serialized_sct())))
}
 
pub fn signed_certificate_timestamp_list_list<'a>(l: Uint1Ffff) -> (o: SignedCertificateTimestampListListCombinator)
    ensures o@ == spec_signed_certificate_timestamp_list_list(l@),
{
    SignedCertificateTimestampListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(serialized_sct())))
}
 

pub closed spec fn spec_signed_certificate_timestamp_list() -> SpecSignedCertificateTimestampListCombinator {
    SpecSignedCertificateTimestampListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ffff(),
            snd: |deps| spec_signed_certificate_timestamp_list_cont(deps),
        },
        mapper: SignedCertificateTimestampListMapper,
    }
)
}

pub open spec fn spec_signed_certificate_timestamp_list_cont(deps: SpecUint1Ffff) -> SpecSignedCertificateTimestampListListCombinator {
    let l = deps;
    spec_signed_certificate_timestamp_list_list(l)
}
 
pub fn signed_certificate_timestamp_list() -> (o: SignedCertificateTimestampListCombinator)
    ensures o@ == spec_signed_certificate_timestamp_list(),
{
    SignedCertificateTimestampListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ffff(),
            snd: SignedCertificateTimestampListCont,
            spec_snd: Ghost(|deps| spec_signed_certificate_timestamp_list_cont(deps)),
        },
        mapper: SignedCertificateTimestampListMapper,
    }
)
}

impl Continuation<Uint1Ffff> for SignedCertificateTimestampListCont {
    type Output = SignedCertificateTimestampListListCombinator;

    open spec fn requires(&self, deps: Uint1Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ffff, o: Self::Output) -> bool {
        o@ == spec_signed_certificate_timestamp_list_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ffff) -> Self::Output {
        let l = deps;
        signed_certificate_timestamp_list_list(l)
    }
}
 

pub closed spec fn spec_certificate_type() -> SpecCertificateTypeCombinator {
    SpecCertificateTypeCombinator(U8)
}
 
pub fn certificate_type() -> (o: CertificateTypeCombinator)
    ensures o@ == spec_certificate_type(),
{
    CertificateTypeCombinator(U8)
}
 

pub closed spec fn spec_client_cert_type_client_extension_types(l: SpecUint1Ff) -> SpecClientCertTypeClientExtensionTypesCombinator {
    SpecClientCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_type())))
}
 
pub fn client_cert_type_client_extension_types(l: Uint1Ff) -> (o: ClientCertTypeClientExtensionTypesCombinator)
    ensures o@ == spec_client_cert_type_client_extension_types(l@),
{
    ClientCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_type())))
}
 

pub closed spec fn spec_client_cert_type_client_extension() -> SpecClientCertTypeClientExtensionCombinator {
    SpecClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_client_cert_type_client_extension_cont(deps),
        },
        mapper: ClientCertTypeClientExtensionMapper,
    }
)
}

pub open spec fn spec_client_cert_type_client_extension_cont(deps: SpecUint1Ff) -> SpecClientCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_client_cert_type_client_extension_types(l)
}
 
pub fn client_cert_type_client_extension() -> (o: ClientCertTypeClientExtensionCombinator)
    ensures o@ == spec_client_cert_type_client_extension(),
{
    ClientCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: ClientCertTypeClientExtensionCont,
            spec_snd: Ghost(|deps| spec_client_cert_type_client_extension_cont(deps)),
        },
        mapper: ClientCertTypeClientExtensionMapper,
    }
)
}

impl Continuation<Uint1Ff> for ClientCertTypeClientExtensionCont {
    type Output = ClientCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_client_cert_type_client_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        client_cert_type_client_extension_types(l)
    }
}
 

pub closed spec fn spec_server_cert_type_client_extension_types(l: SpecUint1Ff) -> SpecServerCertTypeClientExtensionTypesCombinator {
    SpecServerCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_type())))
}
 
pub fn server_cert_type_client_extension_types(l: Uint1Ff) -> (o: ServerCertTypeClientExtensionTypesCombinator)
    ensures o@ == spec_server_cert_type_client_extension_types(l@),
{
    ServerCertTypeClientExtensionTypesCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_type())))
}
 

pub closed spec fn spec_server_cert_type_client_extension() -> SpecServerCertTypeClientExtensionCombinator {
    SpecServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_server_cert_type_client_extension_cont(deps),
        },
        mapper: ServerCertTypeClientExtensionMapper,
    }
)
}

pub open spec fn spec_server_cert_type_client_extension_cont(deps: SpecUint1Ff) -> SpecServerCertTypeClientExtensionTypesCombinator {
    let l = deps;
    spec_server_cert_type_client_extension_types(l)
}
 
pub fn server_cert_type_client_extension() -> (o: ServerCertTypeClientExtensionCombinator)
    ensures o@ == spec_server_cert_type_client_extension(),
{
    ServerCertTypeClientExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: ServerCertTypeClientExtensionCont,
            spec_snd: Ghost(|deps| spec_server_cert_type_client_extension_cont(deps)),
        },
        mapper: ServerCertTypeClientExtensionMapper,
    }
)
}

impl Continuation<Uint1Ff> for ServerCertTypeClientExtensionCont {
    type Output = ServerCertTypeClientExtensionTypesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_server_cert_type_client_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        server_cert_type_client_extension_types(l)
    }
}
 

pub closed spec fn spec_padding_extension() -> SpecPaddingExtensionCombinator {
    SpecPaddingExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_padding_extension_cont(deps),
        },
        mapper: PaddingExtensionMapper,
    }
)
}

pub open spec fn spec_padding_extension_cont(deps: SpecUint0Ffff) -> SpecPaddingExtensionPaddingCombinator {
    let l = deps;
    spec_padding_extension_padding(l)
}
 
pub fn padding_extension() -> (o: PaddingExtensionCombinator)
    ensures o@ == spec_padding_extension(),
{
    PaddingExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: PaddingExtensionCont,
            spec_snd: Ghost(|deps| spec_padding_extension_cont(deps)),
        },
        mapper: PaddingExtensionMapper,
    }
)
}

impl Continuation<Uint0Ffff> for PaddingExtensionCont {
    type Output = PaddingExtensionPaddingCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_padding_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        padding_extension_padding(l)
    }
}
 

pub closed spec fn spec_empty() -> SpecEmptyCombinator {
    SpecEmptyCombinator(BytesN::<0>)
}
 
pub fn empty() -> (o: EmptyCombinator)
    ensures o@ == spec_empty(),
{
    EmptyCombinator(BytesN::<0>)
}
 

pub closed spec fn spec_psk_identity() -> SpecPskIdentityCombinator {
    SpecPskIdentityCombinator(Mapped { inner: (spec_opaque_1_ffff(), U32Be), mapper: PskIdentityMapper })
}
 
pub fn psk_identity() -> (o: PskIdentityCombinator)
    ensures o@ == spec_psk_identity(),
{
    PskIdentityCombinator(Mapped { inner: (opaque_1_ffff(), U32Be), mapper: PskIdentityMapper })
}
 

pub closed spec fn spec_psk_identities_identities(l: u16) -> SpecPskIdentitiesIdentitiesCombinator {
    SpecPskIdentitiesIdentitiesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_identity())))
}
 
pub fn psk_identities_identities<'a>(l: u16) -> (o: PskIdentitiesIdentitiesCombinator)
    ensures o@ == spec_psk_identities_identities(l@),
{
    PskIdentitiesIdentitiesCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_identity())))
}
 

pub closed spec fn spec_psk_identities() -> SpecPskIdentitiesCombinator {
    SpecPskIdentitiesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate17762240283561303569 },
            snd: |deps| spec_psk_identities_cont(deps),
        },
        mapper: PskIdentitiesMapper,
    }
)
}

pub open spec fn spec_psk_identities_cont(deps: u16) -> SpecPskIdentitiesIdentitiesCombinator {
    let l = deps;
    spec_psk_identities_identities(l)
}
 
pub fn psk_identities() -> (o: PskIdentitiesCombinator)
    ensures o@ == spec_psk_identities(),
{
    PskIdentitiesCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate17762240283561303569 },
            snd: PskIdentitiesCont,
            spec_snd: Ghost(|deps| spec_psk_identities_cont(deps)),
        },
        mapper: PskIdentitiesMapper,
    }
)
}

impl Continuation<u16> for PskIdentitiesCont {
    type Output = PskIdentitiesIdentitiesCombinator;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_psk_identities_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        psk_identities_identities(l)
    }
}
 

pub closed spec fn spec_psk_binder_entry() -> SpecPskBinderEntryCombinator {
    SpecPskBinderEntryCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate14956021864372697443 },
            snd: |deps| spec_psk_binder_entry_cont(deps),
        },
        mapper: PskBinderEntryMapper,
    }
)
}

pub open spec fn spec_psk_binder_entry_cont(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn psk_binder_entry() -> (o: PskBinderEntryCombinator)
    ensures o@ == spec_psk_binder_entry(),
{
    PskBinderEntryCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate14956021864372697443 },
            snd: PskBinderEntryCont,
            spec_snd: Ghost(|deps| spec_psk_binder_entry_cont(deps)),
        },
        mapper: PskBinderEntryMapper,
    }
)
}

impl Continuation<u8> for PskBinderEntryCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entry_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_psk_binder_entries_binders(l: u16) -> SpecPskBinderEntriesBindersCombinator {
    SpecPskBinderEntriesBindersCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_psk_binder_entry())))
}
 
pub fn psk_binder_entries_binders<'a>(l: u16) -> (o: PskBinderEntriesBindersCombinator)
    ensures o@ == spec_psk_binder_entries_binders(l@),
{
    PskBinderEntriesBindersCombinator(AndThen(Bytes(l.ex_into()), Repeat(psk_binder_entry())))
}
 

pub closed spec fn spec_psk_binder_entries() -> SpecPskBinderEntriesCombinator {
    SpecPskBinderEntriesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate14504484746533333987 },
            snd: |deps| spec_psk_binder_entries_cont(deps),
        },
        mapper: PskBinderEntriesMapper,
    }
)
}

pub open spec fn spec_psk_binder_entries_cont(deps: u16) -> SpecPskBinderEntriesBindersCombinator {
    let l = deps;
    spec_psk_binder_entries_binders(l)
}
 
pub fn psk_binder_entries() -> (o: PskBinderEntriesCombinator)
    ensures o@ == spec_psk_binder_entries(),
{
    PskBinderEntriesCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate14504484746533333987 },
            snd: PskBinderEntriesCont,
            spec_snd: Ghost(|deps| spec_psk_binder_entries_cont(deps)),
        },
        mapper: PskBinderEntriesMapper,
    }
)
}

impl Continuation<u16> for PskBinderEntriesCont {
    type Output = PskBinderEntriesBindersCombinator;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_psk_binder_entries_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        psk_binder_entries_binders(l)
    }
}
 

pub closed spec fn spec_offered_psks() -> SpecOfferedPsksCombinator {
    SpecOfferedPsksCombinator(Mapped { inner: (spec_psk_identities(), spec_psk_binder_entries()), mapper: OfferedPsksMapper })
}
 
pub fn offered_psks() -> (o: OfferedPsksCombinator)
    ensures o@ == spec_offered_psks(),
{
    OfferedPsksCombinator(Mapped { inner: (psk_identities(), psk_binder_entries()), mapper: OfferedPsksMapper })
}
 

pub closed spec fn spec_pre_shared_key_client_extension() -> SpecPreSharedKeyClientExtensionCombinator {
    SpecPreSharedKeyClientExtensionCombinator(Mapped { inner: spec_offered_psks(), mapper: PreSharedKeyClientExtensionMapper })
}
 
pub fn pre_shared_key_client_extension() -> (o: PreSharedKeyClientExtensionCombinator)
    ensures o@ == spec_pre_shared_key_client_extension(),
{
    PreSharedKeyClientExtensionCombinator(Mapped { inner: offered_psks(), mapper: PreSharedKeyClientExtensionMapper })
}
 

pub closed spec fn spec_supported_versions_client() -> SpecSupportedVersionsClientCombinator {
    SpecSupportedVersionsClientCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate12026843412570934212 },
            snd: |deps| spec_supported_versions_client_cont(deps),
        },
        mapper: SupportedVersionsClientMapper,
    }
)
}

pub open spec fn spec_supported_versions_client_cont(deps: u8) -> SpecSupportedVersionsClientVersionsCombinator {
    let l = deps;
    spec_supported_versions_client_versions(l)
}
 
pub fn supported_versions_client() -> (o: SupportedVersionsClientCombinator)
    ensures o@ == spec_supported_versions_client(),
{
    SupportedVersionsClientCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate12026843412570934212 },
            snd: SupportedVersionsClientCont,
            spec_snd: Ghost(|deps| spec_supported_versions_client_cont(deps)),
        },
        mapper: SupportedVersionsClientMapper,
    }
)
}

impl Continuation<u8> for SupportedVersionsClientCont {
    type Output = SupportedVersionsClientVersionsCombinator;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_supported_versions_client_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
        supported_versions_client_versions(l)
    }
}
 

pub closed spec fn spec_cookie() -> SpecCookieCombinator {
    SpecCookieCombinator(spec_opaque_1_ffff())
}
 
pub fn cookie() -> (o: CookieCombinator)
    ensures o@ == spec_cookie(),
{
    CookieCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_psk_key_exchange_modes() -> SpecPskKeyExchangeModesCombinator {
    SpecPskKeyExchangeModesCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_1_ff(),
            snd: |deps| spec_psk_key_exchange_modes_cont(deps),
        },
        mapper: PskKeyExchangeModesMapper,
    }
)
}

pub open spec fn spec_psk_key_exchange_modes_cont(deps: SpecUint1Ff) -> SpecPskKeyExchangeModesModesCombinator {
    let l = deps;
    spec_psk_key_exchange_modes_modes(l)
}
 
pub fn psk_key_exchange_modes() -> (o: PskKeyExchangeModesCombinator)
    ensures o@ == spec_psk_key_exchange_modes(),
{
    PskKeyExchangeModesCombinator(
    Mapped {
        inner: Depend {
            fst: uint_1_ff(),
            snd: PskKeyExchangeModesCont,
            spec_snd: Ghost(|deps| spec_psk_key_exchange_modes_cont(deps)),
        },
        mapper: PskKeyExchangeModesMapper,
    }
)
}

impl Continuation<Uint1Ff> for PskKeyExchangeModesCont {
    type Output = PskKeyExchangeModesModesCombinator;

    open spec fn requires(&self, deps: Uint1Ff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint1Ff, o: Self::Output) -> bool {
        o@ == spec_psk_key_exchange_modes_cont(deps@)
    }

    fn apply(&self, deps: Uint1Ff) -> Self::Output {
        let l = deps;
        psk_key_exchange_modes_modes(l)
    }
}
 

pub closed spec fn spec_distinguished_name() -> SpecDistinguishedNameCombinator {
    SpecDistinguishedNameCombinator(spec_opaque_1_ffff())
}
 
pub fn distinguished_name() -> (o: DistinguishedNameCombinator)
    ensures o@ == spec_distinguished_name(),
{
    DistinguishedNameCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_certificate_authorities_extension_authorities(l: u16) -> SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    SpecCertificateAuthoritiesExtensionAuthoritiesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_distinguished_name())))
}
 
pub fn certificate_authorities_extension_authorities<'a>(l: u16) -> (o: CertificateAuthoritiesExtensionAuthoritiesCombinator)
    ensures o@ == spec_certificate_authorities_extension_authorities(l@),
{
    CertificateAuthoritiesExtensionAuthoritiesCombinator(AndThen(Bytes(l.ex_into()), Repeat(distinguished_name())))
}
 

pub closed spec fn spec_certificate_authorities_extension() -> SpecCertificateAuthoritiesExtensionCombinator {
    SpecCertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate17709910934222271310 },
            snd: |deps| spec_certificate_authorities_extension_cont(deps),
        },
        mapper: CertificateAuthoritiesExtensionMapper,
    }
)
}

pub open spec fn spec_certificate_authorities_extension_cont(deps: u16) -> SpecCertificateAuthoritiesExtensionAuthoritiesCombinator {
    let l = deps;
    spec_certificate_authorities_extension_authorities(l)
}
 
pub fn certificate_authorities_extension() -> (o: CertificateAuthoritiesExtensionCombinator)
    ensures o@ == spec_certificate_authorities_extension(),
{
    CertificateAuthoritiesExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate17709910934222271310 },
            snd: CertificateAuthoritiesExtensionCont,
            spec_snd: Ghost(|deps| spec_certificate_authorities_extension_cont(deps)),
        },
        mapper: CertificateAuthoritiesExtensionMapper,
    }
)
}

impl Continuation<u16> for CertificateAuthoritiesExtensionCont {
    type Output = CertificateAuthoritiesExtensionAuthoritiesCombinator;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_certificate_authorities_extension_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        certificate_authorities_extension_authorities(l)
    }
}
 

pub closed spec fn spec_oid_filter() -> SpecOidFilterCombinator {
    SpecOidFilterCombinator(Mapped { inner: (spec_opaque_1_ff(), spec_opaque_0_ffff()), mapper: OidFilterMapper })
}
 
pub fn oid_filter() -> (o: OidFilterCombinator)
    ensures o@ == spec_oid_filter(),
{
    OidFilterCombinator(Mapped { inner: (opaque_1_ff(), opaque_0_ffff()), mapper: OidFilterMapper })
}
 

pub closed spec fn spec_oid_filter_extension_filters(l: SpecUint0Ffff) -> SpecOidFilterExtensionFiltersCombinator {
    SpecOidFilterExtensionFiltersCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_oid_filter())))
}
 
pub fn oid_filter_extension_filters<'a>(l: Uint0Ffff) -> (o: OidFilterExtensionFiltersCombinator)
    ensures o@ == spec_oid_filter_extension_filters(l@),
{
    OidFilterExtensionFiltersCombinator(AndThen(Bytes(l.ex_into()), Repeat(oid_filter())))
}
 

pub closed spec fn spec_oid_filter_extension() -> SpecOidFilterExtensionCombinator {
    SpecOidFilterExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_oid_filter_extension_cont(deps),
        },
        mapper: OidFilterExtensionMapper,
    }
)
}

pub open spec fn spec_oid_filter_extension_cont(deps: SpecUint0Ffff) -> SpecOidFilterExtensionFiltersCombinator {
    let l = deps;
    spec_oid_filter_extension_filters(l)
}
 
pub fn oid_filter_extension() -> (o: OidFilterExtensionCombinator)
    ensures o@ == spec_oid_filter_extension(),
{
    OidFilterExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: OidFilterExtensionCont,
            spec_snd: Ghost(|deps| spec_oid_filter_extension_cont(deps)),
        },
        mapper: OidFilterExtensionMapper,
    }
)
}

impl Continuation<Uint0Ffff> for OidFilterExtensionCont {
    type Output = OidFilterExtensionFiltersCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_oid_filter_extension_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        oid_filter_extension_filters(l)
    }
}
 

pub closed spec fn spec_uncompressed_point_representation32() -> SpecUncompressedPointRepresentation32Combinator {
    SpecUncompressedPointRepresentation32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)), mapper: UncompressedPointRepresentation32Mapper })
}
 
pub fn uncompressed_point_representation32() -> (o: UncompressedPointRepresentation32Combinator)
    ensures o@ == spec_uncompressed_point_representation32(),
{
    UncompressedPointRepresentation32Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION32_LEGACY_FORM) }, (BytesN::<32>, BytesN::<32>)), mapper: UncompressedPointRepresentation32Mapper })
}
 

pub closed spec fn spec_uncompressed_point_representation48() -> SpecUncompressedPointRepresentation48Combinator {
    SpecUncompressedPointRepresentation48Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)), mapper: UncompressedPointRepresentation48Mapper })
}
 
pub fn uncompressed_point_representation48() -> (o: UncompressedPointRepresentation48Combinator)
    ensures o@ == spec_uncompressed_point_representation48(),
{
    UncompressedPointRepresentation48Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION48_LEGACY_FORM) }, (BytesN::<48>, BytesN::<48>)), mapper: UncompressedPointRepresentation48Mapper })
}
 

pub closed spec fn spec_uncompressed_point_representation66() -> SpecUncompressedPointRepresentation66Combinator {
    SpecUncompressedPointRepresentation66Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)), mapper: UncompressedPointRepresentation66Mapper })
}
 
pub fn uncompressed_point_representation66() -> (o: UncompressedPointRepresentation66Combinator)
    ensures o@ == spec_uncompressed_point_representation66(),
{
    UncompressedPointRepresentation66Combinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(UNCOMPRESSEDPOINTREPRESENTATION66_LEGACY_FORM) }, (BytesN::<66>, BytesN::<66>)), mapper: UncompressedPointRepresentation66Mapper })
}
 

pub closed spec fn spec_montgomery_point32() -> SpecMontgomeryPoint32Combinator {
    SpecMontgomeryPoint32Combinator(BytesN::<32>)
}
 
pub fn montgomery_point32() -> (o: MontgomeryPoint32Combinator)
    ensures o@ == spec_montgomery_point32(),
{
    MontgomeryPoint32Combinator(BytesN::<32>)
}
 

pub closed spec fn spec_montgomery_form56() -> SpecMontgomeryForm56Combinator {
    SpecMontgomeryForm56Combinator(BytesN::<56>)
}
 
pub fn montgomery_form56() -> (o: MontgomeryForm56Combinator)
    ensures o@ == spec_montgomery_form56(),
{
    MontgomeryForm56Combinator(BytesN::<56>)
}
 

pub closed spec fn spec_sever_dh_params() -> SpecSeverDhParamsCombinator {
    SpecSeverDhParamsCombinator(Mapped { inner: (spec_opaque_1_ffff(), (spec_opaque_1_ffff(), spec_opaque_1_ffff())), mapper: SeverDhParamsMapper })
}
 
pub fn sever_dh_params() -> (o: SeverDhParamsCombinator)
    ensures o@ == spec_sever_dh_params(),
{
    SeverDhParamsCombinator(Mapped { inner: (opaque_1_ffff(), (opaque_1_ffff(), opaque_1_ffff())), mapper: SeverDhParamsMapper })
}
 

pub closed spec fn spec_key_exchange_data() -> SpecKeyExchangeDataCombinator {
    SpecKeyExchangeDataCombinator(spec_opaque_1_ffff())
}
 
pub fn key_exchange_data() -> (o: KeyExchangeDataCombinator)
    ensures o@ == spec_key_exchange_data(),
{
    KeyExchangeDataCombinator(opaque_1_ffff())
}
 

pub closed spec fn spec_key_share_entry_key_exchange(l: SpecUint1Ffff, group: SpecNamedGroup) -> SpecKeyShareEntryKeyExchangeCombinator {
    SpecKeyShareEntryKeyExchangeCombinator(AndThen(Bytes(l.spec_into()), Mapped { inner: OrdChoice(Cond { cond: group == 23, inner: spec_uncompressed_point_representation32() }, OrdChoice(Cond { cond: group == 24, inner: spec_uncompressed_point_representation48() }, OrdChoice(Cond { cond: group == 25, inner: spec_uncompressed_point_representation66() }, OrdChoice(Cond { cond: group == 29, inner: spec_montgomery_point32() }, OrdChoice(Cond { cond: group == 30, inner: spec_montgomery_form56() }, OrdChoice(Cond { cond: group == 256, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 257, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 258, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 259, inner: spec_sever_dh_params() }, OrdChoice(Cond { cond: group == 260, inner: spec_sever_dh_params() }, Cond { cond: !(group == 1 || group == 2 || group == 3 || group == 4 || group == 5 || group == 6 || group == 7 || group == 8 || group == 9 || group == 10 || group == 11 || group == 12 || group == 13 || group == 14 || group == 15 || group == 16 || group == 17 || group == 18 || group == 19 || group == 20 || group == 21 || group == 22 || group == 23 || group == 24 || group == 25 || group == 29 || group == 30 || group == 256 || group == 257 || group == 258 || group == 259 || group == 260), inner: spec_key_exchange_data() })))))))))), mapper: KeyShareEntryKeyExchangeMapper }))
}
 
pub fn key_share_entry_key_exchange<'a>(l: Uint1Ffff, group: NamedGroup) -> (o: KeyShareEntryKeyExchangeCombinator)
    ensures o@ == spec_key_share_entry_key_exchange(l@, group@),
{
    KeyShareEntryKeyExchangeCombinator(AndThen(Bytes(l.ex_into()), Mapped { inner: OrdChoice(Cond { cond: group == 23, inner: uncompressed_point_representation32() }, OrdChoice(Cond { cond: group == 24, inner: uncompressed_point_representation48() }, OrdChoice(Cond { cond: group == 25, inner: uncompressed_point_representation66() }, OrdChoice(Cond { cond: group == 29, inner: montgomery_point32() }, OrdChoice(Cond { cond: group == 30, inner: montgomery_form56() }, OrdChoice(Cond { cond: group == 256, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 257, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 258, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 259, inner: sever_dh_params() }, OrdChoice(Cond { cond: group == 260, inner: sever_dh_params() }, Cond { cond: !(group == 1 || group == 2 || group == 3 || group == 4 || group == 5 || group == 6 || group == 7 || group == 8 || group == 9 || group == 10 || group == 11 || group == 12 || group == 13 || group == 14 || group == 15 || group == 16 || group == 17 || group == 18 || group == 19 || group == 20 || group == 21 || group == 22 || group == 23 || group == 24 || group == 25 || group == 29 || group == 30 || group == 256 || group == 257 || group == 258 || group == 259 || group == 260), inner: key_exchange_data() })))))))))), mapper: KeyShareEntryKeyExchangeMapper }))
}
 

pub closed spec fn spec_key_share_entry() -> SpecKeyShareEntryCombinator {
    SpecKeyShareEntryCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_named_group(), spec_uint_1_ffff()),
            snd: |deps| spec_key_share_entry_cont(deps),
        },
        mapper: KeyShareEntryMapper,
    }
)
}

pub open spec fn spec_key_share_entry_cont(deps: (SpecNamedGroup, SpecUint1Ffff)) -> SpecKeyShareEntryKeyExchangeCombinator {
    let (group, l) = deps;
    spec_key_share_entry_key_exchange(l, group)
}
 
pub fn key_share_entry() -> (o: KeyShareEntryCombinator)
    ensures o@ == spec_key_share_entry(),
{
    KeyShareEntryCombinator(
    Mapped {
        inner: Depend {
            fst: (named_group(), uint_1_ffff()),
            snd: KeyShareEntryCont,
            spec_snd: Ghost(|deps| spec_key_share_entry_cont(deps)),
        },
        mapper: KeyShareEntryMapper,
    }
)
}

impl Continuation<(NamedGroup, Uint1Ffff)> for KeyShareEntryCont {
    type Output = KeyShareEntryKeyExchangeCombinator;

    open spec fn requires(&self, deps: (NamedGroup, Uint1Ffff)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (NamedGroup, Uint1Ffff), o: Self::Output) -> bool {
        o@ == spec_key_share_entry_cont(deps@)
    }

    fn apply(&self, deps: (NamedGroup, Uint1Ffff)) -> Self::Output {
        let (group, l) = deps;
        key_share_entry_key_exchange(l, group)
    }
}
 

pub closed spec fn spec_key_share_client_hello_client_shares(l: SpecUint0Ffff) -> SpecKeyShareClientHelloClientSharesCombinator {
    SpecKeyShareClientHelloClientSharesCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_key_share_entry())))
}
 
pub fn key_share_client_hello_client_shares<'a>(l: Uint0Ffff) -> (o: KeyShareClientHelloClientSharesCombinator)
    ensures o@ == spec_key_share_client_hello_client_shares(l@),
{
    KeyShareClientHelloClientSharesCombinator(AndThen(Bytes(l.ex_into()), Repeat(key_share_entry())))
}
 

pub closed spec fn spec_key_share_client_hello() -> SpecKeyShareClientHelloCombinator {
    SpecKeyShareClientHelloCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_key_share_client_hello_cont(deps),
        },
        mapper: KeyShareClientHelloMapper,
    }
)
}

pub open spec fn spec_key_share_client_hello_cont(deps: SpecUint0Ffff) -> SpecKeyShareClientHelloClientSharesCombinator {
    let l = deps;
    spec_key_share_client_hello_client_shares(l)
}
 
pub fn key_share_client_hello() -> (o: KeyShareClientHelloCombinator)
    ensures o@ == spec_key_share_client_hello(),
{
    KeyShareClientHelloCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: KeyShareClientHelloCont,
            spec_snd: Ghost(|deps| spec_key_share_client_hello_cont(deps)),
        },
        mapper: KeyShareClientHelloMapper,
    }
)
}

impl Continuation<Uint0Ffff> for KeyShareClientHelloCont {
    type Output = KeyShareClientHelloClientSharesCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_key_share_client_hello_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        key_share_client_hello_client_shares(l)
    }
}
 

pub closed spec fn spec_client_hello_extension_extension_data(extension_type: SpecExtensionType, ext_len: u16) -> SpecClientHelloExtensionExtensionDataCombinator {
    SpecClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: spec_ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: spec_use_srtp_data() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: spec_padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: Bytes(ext_len.spec_into()) }, OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) })))))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper }))
}
 
pub fn client_hello_extension_extension_data<'a>(extension_type: ExtensionType, ext_len: u16) -> (o: ClientHelloExtensionExtensionDataCombinator)
    ensures o@ == spec_client_hello_extension_extension_data(extension_type@, ext_len@),
{
    ClientHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: use_srtp_data() }, OrdChoice(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: Bytes(ext_len.ex_into()) }, OrdChoice(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) })))))))))))))))))))))))))), mapper: ClientHelloExtensionExtensionDataMapper }))
}
 

pub closed spec fn spec_uint_0_fffe() -> SpecUint0FffeCombinator {
    SpecUint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate184937773087435626 })
}
 
pub fn uint_0_fffe() -> (o: Uint0FffeCombinator)
    ensures o@ == spec_uint_0_fffe(),
{
    Uint0FffeCombinator(Refined { inner: U16Be, predicate: Predicate184937773087435626 })
}
 

pub closed spec fn spec_key_update_request() -> SpecKeyUpdateRequestCombinator {
    SpecKeyUpdateRequestCombinator(TryMap { inner: U8, mapper: KeyUpdateRequestMapper })
}
 
pub fn key_update_request() -> (o: KeyUpdateRequestCombinator)
    ensures o@ == spec_key_update_request(),
{
    KeyUpdateRequestCombinator(TryMap { inner: U8, mapper: KeyUpdateRequestMapper })
}
 

pub closed spec fn spec_key_update() -> SpecKeyUpdateCombinator {
    SpecKeyUpdateCombinator(Mapped { inner: spec_key_update_request(), mapper: KeyUpdateMapper })
}
 
pub fn key_update() -> (o: KeyUpdateCombinator)
    ensures o@ == spec_key_update(),
{
    KeyUpdateCombinator(Mapped { inner: key_update_request(), mapper: KeyUpdateMapper })
}
 

pub closed spec fn spec_supported_versions_server() -> SpecSupportedVersionsServerCombinator {
    SpecSupportedVersionsServerCombinator(Mapped { inner: spec_protocol_version(), mapper: SupportedVersionsServerMapper })
}
 
pub fn supported_versions_server() -> (o: SupportedVersionsServerCombinator)
    ensures o@ == spec_supported_versions_server(),
{
    SupportedVersionsServerCombinator(Mapped { inner: protocol_version(), mapper: SupportedVersionsServerMapper })
}
 

pub closed spec fn spec_opaque_1_ffffff() -> SpecOpaque1FfffffCombinator {
    SpecOpaque1FfffffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U24Be, predicate: Predicate10565972399076720534 },
            snd: |deps| spec_opaque1_ffffff_cont(deps),
        },
        mapper: Opaque1FfffffMapper,
    }
)
}

pub open spec fn spec_opaque1_ffffff_cont(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_1_ffffff() -> (o: Opaque1FfffffCombinator)
    ensures o@ == spec_opaque_1_ffffff(),
{
    Opaque1FfffffCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U24Be, predicate: Predicate10565972399076720534 },
            snd: Opaque1FfffffCont,
            spec_snd: Ghost(|deps| spec_opaque1_ffffff_cont(deps)),
        },
        mapper: Opaque1FfffffMapper,
    }
)
}

impl Continuation<u24> for Opaque1FfffffCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_opaque1_ffffff_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_encrypted_extensions_extensions(l: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    SpecEncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}
 
pub fn encrypted_extensions_extensions<'a>(l: Uint0Ffff) -> (o: EncryptedExtensionsExtensionsCombinator)
    ensures o@ == spec_encrypted_extensions_extensions(l@),
{
    EncryptedExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
}
 

pub closed spec fn spec_encrypted_extensions() -> SpecEncryptedExtensionsCombinator {
    SpecEncryptedExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_ffff(),
            snd: |deps| spec_encrypted_extensions_cont(deps),
        },
        mapper: EncryptedExtensionsMapper,
    }
)
}

pub open spec fn spec_encrypted_extensions_cont(deps: SpecUint0Ffff) -> SpecEncryptedExtensionsExtensionsCombinator {
    let l = deps;
    spec_encrypted_extensions_extensions(l)
}
 
pub fn encrypted_extensions() -> (o: EncryptedExtensionsCombinator)
    ensures o@ == spec_encrypted_extensions(),
{
    EncryptedExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_ffff(),
            snd: EncryptedExtensionsCont,
            spec_snd: Ghost(|deps| spec_encrypted_extensions_cont(deps)),
        },
        mapper: EncryptedExtensionsMapper,
    }
)
}

impl Continuation<Uint0Ffff> for EncryptedExtensionsCont {
    type Output = EncryptedExtensionsExtensionsCombinator;

    open spec fn requires(&self, deps: Uint0Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Ffff, o: Self::Output) -> bool {
        o@ == spec_encrypted_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint0Ffff) -> Self::Output {
        let l = deps;
        encrypted_extensions_extensions(l)
    }
}
 

pub closed spec fn spec_certificate_extensions() -> SpecCertificateExtensionsCombinator {
    SpecCertificateExtensionsCombinator(spec_encrypted_extensions())
}
 
pub fn certificate_extensions() -> (o: CertificateExtensionsCombinator)
    ensures o@ == spec_certificate_extensions(),
{
    CertificateExtensionsCombinator(encrypted_extensions())
}
 

pub closed spec fn spec_certificate_entry() -> SpecCertificateEntryCombinator {
    SpecCertificateEntryCombinator(Mapped { inner: (spec_opaque_1_ffffff(), spec_certificate_extensions()), mapper: CertificateEntryMapper })
}
 
pub fn certificate_entry() -> (o: CertificateEntryCombinator)
    ensures o@ == spec_certificate_entry(),
{
    CertificateEntryCombinator(Mapped { inner: (opaque_1_ffffff(), certificate_extensions()), mapper: CertificateEntryMapper })
}
 

pub closed spec fn spec_certificate_list_list(l: u24) -> SpecCertificateListListCombinator {
    SpecCertificateListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_certificate_entry())))
}
 
pub fn certificate_list_list<'a>(l: u24) -> (o: CertificateListListCombinator)
    ensures o@ == spec_certificate_list_list(l@),
{
    CertificateListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(certificate_entry())))
}
 

pub closed spec fn spec_certificate_list() -> SpecCertificateListCombinator {
    SpecCertificateListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: U24Be,
            snd: |deps| spec_certificate_list_cont(deps),
        },
        mapper: CertificateListMapper,
    }
)
}

pub open spec fn spec_certificate_list_cont(deps: u24) -> SpecCertificateListListCombinator {
    let l = deps;
    spec_certificate_list_list(l)
}
 
pub fn certificate_list() -> (o: CertificateListCombinator)
    ensures o@ == spec_certificate_list(),
{
    CertificateListCombinator(
    Mapped {
        inner: Depend {
            fst: U24Be,
            snd: CertificateListCont,
            spec_snd: Ghost(|deps| spec_certificate_list_cont(deps)),
        },
        mapper: CertificateListMapper,
    }
)
}

impl Continuation<u24> for CertificateListCont {
    type Output = CertificateListListCombinator;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_certificate_list_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        certificate_list_list(l)
    }
}
 

pub closed spec fn spec_certificate() -> SpecCertificateCombinator {
    SpecCertificateCombinator(Mapped { inner: (spec_opaque_0_ff(), spec_certificate_list()), mapper: CertificateMapper })
}
 
pub fn certificate() -> (o: CertificateCombinator)
    ensures o@ == spec_certificate(),
{
    CertificateCombinator(Mapped { inner: (opaque_0_ff(), certificate_list()), mapper: CertificateMapper })
}
 

pub closed spec fn spec_early_data_indication_new_session_ticket() -> SpecEarlyDataIndicationNewSessionTicketCombinator {
    SpecEarlyDataIndicationNewSessionTicketCombinator(Mapped { inner: U32Be, mapper: EarlyDataIndicationNewSessionTicketMapper })
}
 
pub fn early_data_indication_new_session_ticket() -> (o: EarlyDataIndicationNewSessionTicketCombinator)
    ensures o@ == spec_early_data_indication_new_session_ticket(),
{
    EarlyDataIndicationNewSessionTicketCombinator(Mapped { inner: U32Be, mapper: EarlyDataIndicationNewSessionTicketMapper })
}
 

pub closed spec fn spec_pre_shared_key_server_extension() -> SpecPreSharedKeyServerExtensionCombinator {
    SpecPreSharedKeyServerExtensionCombinator(Mapped { inner: U16Be, mapper: PreSharedKeyServerExtensionMapper })
}
 
pub fn pre_shared_key_server_extension() -> (o: PreSharedKeyServerExtensionCombinator)
    ensures o@ == spec_pre_shared_key_server_extension(),
{
    PreSharedKeyServerExtensionCombinator(Mapped { inner: U16Be, mapper: PreSharedKeyServerExtensionMapper })
}
 

pub closed spec fn spec_random() -> SpecRandomCombinator {
    SpecRandomCombinator(BytesN::<32>)
}
 
pub fn random() -> (o: RandomCombinator)
    ensures o@ == spec_random(),
{
    RandomCombinator(BytesN::<32>)
}
 

pub closed spec fn spec_session_id() -> SpecSessionIdCombinator {
    SpecSessionIdCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U8, predicate: Predicate10693986609604791304 },
            snd: |deps| spec_session_id_cont(deps),
        },
        mapper: SessionIdMapper,
    }
)
}

pub open spec fn spec_session_id_cont(deps: u8) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn session_id() -> (o: SessionIdCombinator)
    ensures o@ == spec_session_id(),
{
    SessionIdCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U8, predicate: Predicate10693986609604791304 },
            snd: SessionIdCont,
            spec_snd: Ghost(|deps| spec_session_id_cont(deps)),
        },
        mapper: SessionIdMapper,
    }
)
}

impl Continuation<u8> for SessionIdCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: u8) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u8, o: Self::Output) -> bool {
        o@ == spec_session_id_cont(deps@)
    }

    fn apply(&self, deps: u8) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_cipher_suite() -> SpecCipherSuiteCombinator {
    SpecCipherSuiteCombinator(U16Be)
}
 
pub fn cipher_suite() -> (o: CipherSuiteCombinator)
    ensures o@ == spec_cipher_suite(),
{
    CipherSuiteCombinator(U16Be)
}
 

pub closed spec fn spec_cipher_suite_list_list(l: SpecUint2Fffe) -> SpecCipherSuiteListListCombinator {
    SpecCipherSuiteListListCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_cipher_suite())))
}
 
pub fn cipher_suite_list_list(l: Uint2Fffe) -> (o: CipherSuiteListListCombinator)
    ensures o@ == spec_cipher_suite_list_list(l@),
{
    CipherSuiteListListCombinator(AndThen(Bytes(l.ex_into()), Repeat(cipher_suite())))
}
 

pub closed spec fn spec_cipher_suite_list() -> SpecCipherSuiteListCombinator {
    SpecCipherSuiteListCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_fffe(),
            snd: |deps| spec_cipher_suite_list_cont(deps),
        },
        mapper: CipherSuiteListMapper,
    }
)
}

pub open spec fn spec_cipher_suite_list_cont(deps: SpecUint2Fffe) -> SpecCipherSuiteListListCombinator {
    let l = deps;
    spec_cipher_suite_list_list(l)
}
 
pub fn cipher_suite_list() -> (o: CipherSuiteListCombinator)
    ensures o@ == spec_cipher_suite_list(),
{
    CipherSuiteListCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_fffe(),
            snd: CipherSuiteListCont,
            spec_snd: Ghost(|deps| spec_cipher_suite_list_cont(deps)),
        },
        mapper: CipherSuiteListMapper,
    }
)
}

impl Continuation<Uint2Fffe> for CipherSuiteListCont {
    type Output = CipherSuiteListListCombinator;

    open spec fn requires(&self, deps: Uint2Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Fffe, o: Self::Output) -> bool {
        o@ == spec_cipher_suite_list_cont(deps@)
    }

    fn apply(&self, deps: Uint2Fffe) -> Self::Output {
        let l = deps;
        cipher_suite_list_list(l)
    }
}
 

pub closed spec fn spec_client_hello_extension() -> SpecClientHelloExtensionCombinator {
    SpecClientHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_extension_type(), U16Be),
            snd: |deps| spec_client_hello_extension_cont(deps),
        },
        mapper: ClientHelloExtensionMapper,
    }
)
}

pub open spec fn spec_client_hello_extension_cont(deps: (SpecExtensionType, u16)) -> SpecClientHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_client_hello_extension_extension_data(extension_type, ext_len)
}
 
pub fn client_hello_extension() -> (o: ClientHelloExtensionCombinator)
    ensures o@ == spec_client_hello_extension(),
{
    ClientHelloExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: (extension_type(), U16Be),
            snd: ClientHelloExtensionCont,
            spec_snd: Ghost(|deps| spec_client_hello_extension_cont(deps)),
        },
        mapper: ClientHelloExtensionMapper,
    }
)
}

impl Continuation<(ExtensionType, u16)> for ClientHelloExtensionCont {
    type Output = ClientHelloExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: (ExtensionType, u16)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_client_hello_extension_cont(deps@)
    }

    fn apply(&self, deps: (ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = deps;
        client_hello_extension_extension_data(extension_type, ext_len)
    }
}
 

pub closed spec fn spec_client_extensions_extensions(l: u16) -> SpecClientExtensionsExtensionsCombinator {
    SpecClientExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_client_hello_extension())))
}
 
pub fn client_extensions_extensions<'a>(l: u16) -> (o: ClientExtensionsExtensionsCombinator)
    ensures o@ == spec_client_extensions_extensions(l@),
{
    ClientExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(client_hello_extension())))
}
 

pub closed spec fn spec_client_extensions() -> SpecClientExtensionsCombinator {
    SpecClientExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate15770232246241775772 },
            snd: |deps| spec_client_extensions_cont(deps),
        },
        mapper: ClientExtensionsMapper,
    }
)
}

pub open spec fn spec_client_extensions_cont(deps: u16) -> SpecClientExtensionsExtensionsCombinator {
    let l = deps;
    spec_client_extensions_extensions(l)
}
 
pub fn client_extensions() -> (o: ClientExtensionsCombinator)
    ensures o@ == spec_client_extensions(),
{
    ClientExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate15770232246241775772 },
            snd: ClientExtensionsCont,
            spec_snd: Ghost(|deps| spec_client_extensions_cont(deps)),
        },
        mapper: ClientExtensionsMapper,
    }
)
}

impl Continuation<u16> for ClientExtensionsCont {
    type Output = ClientExtensionsExtensionsCombinator;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_client_extensions_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        client_extensions_extensions(l)
    }
}
 

pub closed spec fn spec_client_hello() -> SpecClientHelloCombinator {
    SpecClientHelloCombinator(Mapped { inner: (spec_protocol_version(), (spec_random(), (spec_session_id(), (spec_cipher_suite_list(), (spec_opaque_1_ff(), spec_client_extensions()))))), mapper: ClientHelloMapper })
}
 
pub fn client_hello() -> (o: ClientHelloCombinator)
    ensures o@ == spec_client_hello(),
{
    ClientHelloCombinator(Mapped { inner: (protocol_version(), (random(), (session_id(), (cipher_suite_list(), (opaque_1_ff(), client_extensions()))))), mapper: ClientHelloMapper })
}
 

pub closed spec fn spec_certificate_request_extensions_extensions(l: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    SpecCertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_extension())))
}
 
pub fn certificate_request_extensions_extensions<'a>(l: Uint2Ffff) -> (o: CertificateRequestExtensionsExtensionsCombinator)
    ensures o@ == spec_certificate_request_extensions_extensions(l@),
{
    CertificateRequestExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(extension())))
}
 

pub closed spec fn spec_certificate_request_extensions() -> SpecCertificateRequestExtensionsCombinator {
    SpecCertificateRequestExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_certificate_request_extensions_cont(deps),
        },
        mapper: CertificateRequestExtensionsMapper,
    }
)
}

pub open spec fn spec_certificate_request_extensions_cont(deps: SpecUint2Ffff) -> SpecCertificateRequestExtensionsExtensionsCombinator {
    let l = deps;
    spec_certificate_request_extensions_extensions(l)
}
 
pub fn certificate_request_extensions() -> (o: CertificateRequestExtensionsCombinator)
    ensures o@ == spec_certificate_request_extensions(),
{
    CertificateRequestExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: CertificateRequestExtensionsCont,
            spec_snd: Ghost(|deps| spec_certificate_request_extensions_cont(deps)),
        },
        mapper: CertificateRequestExtensionsMapper,
    }
)
}

impl Continuation<Uint2Ffff> for CertificateRequestExtensionsCont {
    type Output = CertificateRequestExtensionsExtensionsCombinator;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_certificate_request_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        certificate_request_extensions_extensions(l)
    }
}
 

pub closed spec fn spec_certificate_request() -> SpecCertificateRequestCombinator {
    SpecCertificateRequestCombinator(Mapped { inner: (spec_opaque_0_ff(), spec_certificate_request_extensions()), mapper: CertificateRequestMapper })
}
 
pub fn certificate_request() -> (o: CertificateRequestCombinator)
    ensures o@ == spec_certificate_request(),
{
    CertificateRequestCombinator(Mapped { inner: (opaque_0_ff(), certificate_request_extensions()), mapper: CertificateRequestMapper })
}
 

pub closed spec fn spec_new_session_ticket_extensions() -> SpecNewSessionTicketExtensionsCombinator {
    SpecNewSessionTicketExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_0_fffe(),
            snd: |deps| spec_new_session_ticket_extensions_cont(deps),
        },
        mapper: NewSessionTicketExtensionsMapper,
    }
)
}

pub open spec fn spec_new_session_ticket_extensions_cont(deps: SpecUint0Fffe) -> SpecNewSessionTicketExtensionsExtensionsCombinator {
    let l = deps;
    spec_new_session_ticket_extensions_extensions(l)
}
 
pub fn new_session_ticket_extensions() -> (o: NewSessionTicketExtensionsCombinator)
    ensures o@ == spec_new_session_ticket_extensions(),
{
    NewSessionTicketExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: uint_0_fffe(),
            snd: NewSessionTicketExtensionsCont,
            spec_snd: Ghost(|deps| spec_new_session_ticket_extensions_cont(deps)),
        },
        mapper: NewSessionTicketExtensionsMapper,
    }
)
}

impl Continuation<Uint0Fffe> for NewSessionTicketExtensionsCont {
    type Output = NewSessionTicketExtensionsExtensionsCombinator;

    open spec fn requires(&self, deps: Uint0Fffe) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint0Fffe, o: Self::Output) -> bool {
        o@ == spec_new_session_ticket_extensions_cont(deps@)
    }

    fn apply(&self, deps: Uint0Fffe) -> Self::Output {
        let l = deps;
        new_session_ticket_extensions_extensions(l)
    }
}
 

pub closed spec fn spec_new_session_ticket() -> SpecNewSessionTicketCombinator {
    SpecNewSessionTicketCombinator(Mapped { inner: (U32Be, (U32Be, (spec_opaque_0_ff(), (spec_opaque_1_ffff(), spec_new_session_ticket_extensions())))), mapper: NewSessionTicketMapper })
}
 
pub fn new_session_ticket() -> (o: NewSessionTicketCombinator)
    ensures o@ == spec_new_session_ticket(),
{
    NewSessionTicketCombinator(Mapped { inner: (U32Be, (U32Be, (opaque_0_ff(), (opaque_1_ffff(), new_session_ticket_extensions())))), mapper: NewSessionTicketMapper })
}
 

pub closed spec fn spec_certificate_verify() -> SpecCertificateVerifyCombinator {
    SpecCertificateVerifyCombinator(Mapped { inner: (spec_signature_scheme(), spec_opaque_0_ffff()), mapper: CertificateVerifyMapper })
}
 
pub fn certificate_verify() -> (o: CertificateVerifyCombinator)
    ensures o@ == spec_certificate_verify(),
{
    CertificateVerifyCombinator(Mapped { inner: (signature_scheme(), opaque_0_ffff()), mapper: CertificateVerifyMapper })
}
 

pub closed spec fn spec_content_type() -> SpecContentTypeCombinator {
    SpecContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}
 
pub fn content_type() -> (o: ContentTypeCombinator)
    ensures o@ == spec_content_type(),
{
    ContentTypeCombinator(TryMap { inner: U8, mapper: ContentTypeMapper })
}
 

pub closed spec fn spec_tls_plaintext() -> SpecTlsPlaintextCombinator {
    SpecTlsPlaintextCombinator(Mapped { inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())), mapper: TlsPlaintextMapper })
}
 
pub fn tls_plaintext() -> (o: TlsPlaintextCombinator)
    ensures o@ == spec_tls_plaintext(),
{
    TlsPlaintextCombinator(Mapped { inner: (content_type(), (protocol_version(), opaque_0_ffff())), mapper: TlsPlaintextMapper })
}
 

pub closed spec fn spec_sever_hello_extension_extension_data(ext_len: u16, extension_type: SpecExtensionType) -> SpecSeverHelloExtensionExtensionDataCombinator {
    SpecSeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.spec_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: spec_server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: spec_max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: spec_certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: spec_named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: spec_ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: spec_srtp_protection_profiles() }, OrdChoice(Cond { cond: extension_type == 15, inner: spec_heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: spec_protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: spec_signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: spec_client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: spec_server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: spec_padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 41, inner: spec_pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: spec_supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: spec_cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: spec_psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: spec_certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: spec_oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: spec_empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: spec_signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: spec_key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.spec_into()) })))))))))))))))))))))))))), mapper: SeverHelloExtensionExtensionDataMapper }))
}
 
pub fn sever_hello_extension_extension_data<'a>(ext_len: u16, extension_type: ExtensionType) -> (o: SeverHelloExtensionExtensionDataCombinator)
    ensures o@ == spec_sever_hello_extension_extension_data(ext_len@, extension_type@),
{
    SeverHelloExtensionExtensionDataCombinator(AndThen(Bytes(ext_len.ex_into()), Mapped { inner: OrdChoice(Cond { cond: extension_type == 0, inner: server_name_list() }, OrdChoice(Cond { cond: extension_type == 1, inner: max_fragment_length() }, OrdChoice(Cond { cond: extension_type == 5, inner: certificate_status_request() }, OrdChoice(Cond { cond: extension_type == 10, inner: named_group_list() }, OrdChoice(Cond { cond: extension_type == 11, inner: ec_point_format_list() }, OrdChoice(Cond { cond: extension_type == 13, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 14, inner: srtp_protection_profiles() }, OrdChoice(Cond { cond: extension_type == 15, inner: heartbeat_mode() }, OrdChoice(Cond { cond: extension_type == 16, inner: protocol_name_list() }, OrdChoice(Cond { cond: extension_type == 18, inner: signed_certificate_timestamp_list() }, OrdChoice(Cond { cond: extension_type == 19, inner: client_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 20, inner: server_cert_type_client_extension() }, OrdChoice(Cond { cond: extension_type == 21, inner: padding_extension() }, OrdChoice(Cond { cond: extension_type == 22, inner: empty() }, OrdChoice(Cond { cond: extension_type == 23, inner: empty() }, OrdChoice(Cond { cond: extension_type == 35, inner: empty() }, OrdChoice(Cond { cond: extension_type == 41, inner: pre_shared_key_client_extension() }, OrdChoice(Cond { cond: extension_type == 42, inner: empty() }, OrdChoice(Cond { cond: extension_type == 43, inner: supported_versions_client() }, OrdChoice(Cond { cond: extension_type == 44, inner: cookie() }, OrdChoice(Cond { cond: extension_type == 45, inner: psk_key_exchange_modes() }, OrdChoice(Cond { cond: extension_type == 47, inner: certificate_authorities_extension() }, OrdChoice(Cond { cond: extension_type == 48, inner: oid_filter_extension() }, OrdChoice(Cond { cond: extension_type == 49, inner: empty() }, OrdChoice(Cond { cond: extension_type == 50, inner: signature_scheme_list() }, OrdChoice(Cond { cond: extension_type == 51, inner: key_share_client_hello() }, Cond { cond: !(extension_type == 0 || extension_type == 1 || extension_type == 5 || extension_type == 10 || extension_type == 11 || extension_type == 13 || extension_type == 14 || extension_type == 15 || extension_type == 16 || extension_type == 18 || extension_type == 19 || extension_type == 20 || extension_type == 21 || extension_type == 22 || extension_type == 23 || extension_type == 35 || extension_type == 41 || extension_type == 42 || extension_type == 43 || extension_type == 44 || extension_type == 45 || extension_type == 47 || extension_type == 48 || extension_type == 49 || extension_type == 50 || extension_type == 51 || extension_type == 65535), inner: Bytes(ext_len.ex_into()) })))))))))))))))))))))))))), mapper: SeverHelloExtensionExtensionDataMapper }))
}
 

pub closed spec fn spec_sever_hello_extension() -> SpecSeverHelloExtensionCombinator {
    SpecSeverHelloExtensionCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_extension_type(), U16Be),
            snd: |deps| spec_sever_hello_extension_cont(deps),
        },
        mapper: SeverHelloExtensionMapper,
    }
)
}

pub open spec fn spec_sever_hello_extension_cont(deps: (SpecExtensionType, u16)) -> SpecSeverHelloExtensionExtensionDataCombinator {
    let (extension_type, ext_len) = deps;
    spec_sever_hello_extension_extension_data(ext_len, extension_type)
}
 
pub fn sever_hello_extension() -> (o: SeverHelloExtensionCombinator)
    ensures o@ == spec_sever_hello_extension(),
{
    SeverHelloExtensionCombinator(
    Mapped {
        inner: Depend {
            fst: (extension_type(), U16Be),
            snd: SeverHelloExtensionCont,
            spec_snd: Ghost(|deps| spec_sever_hello_extension_cont(deps)),
        },
        mapper: SeverHelloExtensionMapper,
    }
)
}

impl Continuation<(ExtensionType, u16)> for SeverHelloExtensionCont {
    type Output = SeverHelloExtensionExtensionDataCombinator;

    open spec fn requires(&self, deps: (ExtensionType, u16)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (ExtensionType, u16), o: Self::Output) -> bool {
        o@ == spec_sever_hello_extension_cont(deps@)
    }

    fn apply(&self, deps: (ExtensionType, u16)) -> Self::Output {
        let (extension_type, ext_len) = deps;
        sever_hello_extension_extension_data(ext_len, extension_type)
    }
}
 

pub closed spec fn spec_handshake_type() -> SpecHandshakeTypeCombinator {
    SpecHandshakeTypeCombinator(TryMap { inner: U8, mapper: HandshakeTypeMapper })
}
 
pub fn handshake_type() -> (o: HandshakeTypeCombinator)
    ensures o@ == spec_handshake_type(),
{
    HandshakeTypeCombinator(TryMap { inner: U8, mapper: HandshakeTypeMapper })
}
 

pub closed spec fn spec_server_extensions_extensions(l: u16) -> SpecServerExtensionsExtensionsCombinator {
    SpecServerExtensionsExtensionsCombinator(AndThen(Bytes(l.spec_into()), Repeat(spec_sever_hello_extension())))
}
 
pub fn server_extensions_extensions<'a>(l: u16) -> (o: ServerExtensionsExtensionsCombinator)
    ensures o@ == spec_server_extensions_extensions(l@),
{
    ServerExtensionsExtensionsCombinator(AndThen(Bytes(l.ex_into()), Repeat(sever_hello_extension())))
}
 

pub closed spec fn spec_server_extensions() -> SpecServerExtensionsCombinator {
    SpecServerExtensionsCombinator(
    Mapped {
        inner: SpecDepend {
            fst: Refined { inner: U16Be, predicate: Predicate503472032047519273 },
            snd: |deps| spec_server_extensions_cont(deps),
        },
        mapper: ServerExtensionsMapper,
    }
)
}

pub open spec fn spec_server_extensions_cont(deps: u16) -> SpecServerExtensionsExtensionsCombinator {
    let l = deps;
    spec_server_extensions_extensions(l)
}
 
pub fn server_extensions() -> (o: ServerExtensionsCombinator)
    ensures o@ == spec_server_extensions(),
{
    ServerExtensionsCombinator(
    Mapped {
        inner: Depend {
            fst: Refined { inner: U16Be, predicate: Predicate503472032047519273 },
            snd: ServerExtensionsCont,
            spec_snd: Ghost(|deps| spec_server_extensions_cont(deps)),
        },
        mapper: ServerExtensionsMapper,
    }
)
}

impl Continuation<u16> for ServerExtensionsCont {
    type Output = ServerExtensionsExtensionsCombinator;

    open spec fn requires(&self, deps: u16) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u16, o: Self::Output) -> bool {
        o@ == spec_server_extensions_cont(deps@)
    }

    fn apply(&self, deps: u16) -> Self::Output {
        let l = deps;
        server_extensions_extensions(l)
    }
}
 

pub closed spec fn spec_server_hello() -> SpecServerHelloCombinator {
    SpecServerHelloCombinator(Mapped { inner: (spec_protocol_version(), (spec_random(), (spec_session_id(), (spec_cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, spec_server_extensions()))))), mapper: ServerHelloMapper })
}
 
pub fn server_hello() -> (o: ServerHelloCombinator)
    ensures o@ == spec_server_hello(),
{
    ServerHelloCombinator(Mapped { inner: (protocol_version(), (random(), (session_id(), (cipher_suite(), (Refined { inner: U8, predicate: TagPred(SERVERHELLO_LEGACY_COMPRESSION_METHOD) }, server_extensions()))))), mapper: ServerHelloMapper })
}
 

pub closed spec fn spec_finished(digest_size: u24) -> SpecFinishedCombinator {
    SpecFinishedCombinator(Bytes(digest_size.spec_into()))
}
 
pub fn finished<'a>(digest_size: u24) -> (o: FinishedCombinator)
    ensures o@ == spec_finished(digest_size@),
{
    FinishedCombinator(Bytes(digest_size.ex_into()))
}
 

pub closed spec fn spec_handshake_msg(length: u24, msg_type: SpecHandshakeType) -> SpecHandshakeMsgCombinator {
    SpecHandshakeMsgCombinator(AndThen(Bytes(length.spec_into()), Mapped { inner: OrdChoice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: spec_client_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: spec_server_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: spec_new_session_ticket() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: spec_empty() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: spec_encrypted_extensions() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Certificate, inner: spec_certificate() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: spec_certificate_request() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: spec_certificate_verify() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Finished, inner: spec_finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: spec_key_update() }))))))))), mapper: HandshakeMsgMapper }))
}
 
pub fn handshake_msg<'a>(length: u24, msg_type: HandshakeType) -> (o: HandshakeMsgCombinator)
    ensures o@ == spec_handshake_msg(length@, msg_type@),
{
    HandshakeMsgCombinator(AndThen(Bytes(length.ex_into()), Mapped { inner: OrdChoice(Cond { cond: msg_type == HandshakeType::ClientHello, inner: client_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::ServerHello, inner: server_hello() }, OrdChoice(Cond { cond: msg_type == HandshakeType::NewSessionTicket, inner: new_session_ticket() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EndOfEarlyData, inner: empty() }, OrdChoice(Cond { cond: msg_type == HandshakeType::EncryptedExtensions, inner: encrypted_extensions() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Certificate, inner: certificate() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateRequest, inner: certificate_request() }, OrdChoice(Cond { cond: msg_type == HandshakeType::CertificateVerify, inner: certificate_verify() }, OrdChoice(Cond { cond: msg_type == HandshakeType::Finished, inner: finished(length) }, Cond { cond: msg_type == HandshakeType::KeyUpdate, inner: key_update() }))))))))), mapper: HandshakeMsgMapper }))
}
 

pub closed spec fn spec_handshake() -> SpecHandshakeCombinator {
    SpecHandshakeCombinator(
    Mapped {
        inner: SpecDepend {
            fst: (spec_handshake_type(), U24Be),
            snd: |deps| spec_handshake_cont(deps),
        },
        mapper: HandshakeMapper,
    }
)
}

pub open spec fn spec_handshake_cont(deps: (SpecHandshakeType, u24)) -> SpecHandshakeMsgCombinator {
    let (msg_type, length) = deps;
    spec_handshake_msg(length, msg_type)
}
 
pub fn handshake() -> (o: HandshakeCombinator)
    ensures o@ == spec_handshake(),
{
    HandshakeCombinator(
    Mapped {
        inner: Depend {
            fst: (handshake_type(), U24Be),
            snd: HandshakeCont,
            spec_snd: Ghost(|deps| spec_handshake_cont(deps)),
        },
        mapper: HandshakeMapper,
    }
)
}

impl Continuation<(HandshakeType, u24)> for HandshakeCont {
    type Output = HandshakeMsgCombinator;

    open spec fn requires(&self, deps: (HandshakeType, u24)) -> bool {
        true
    }

    open spec fn ensures(&self, deps: (HandshakeType, u24), o: Self::Output) -> bool {
        o@ == spec_handshake_cont(deps@)
    }

    fn apply(&self, deps: (HandshakeType, u24)) -> Self::Output {
        let (msg_type, length) = deps;
        handshake_msg(length, msg_type)
    }
}
 

pub closed spec fn spec_server_cert_type_server_extension() -> SpecServerCertTypeServerExtensionCombinator {
    SpecServerCertTypeServerExtensionCombinator(Mapped { inner: spec_certificate_type(), mapper: ServerCertTypeServerExtensionMapper })
}
 
pub fn server_cert_type_server_extension() -> (o: ServerCertTypeServerExtensionCombinator)
    ensures o@ == spec_server_cert_type_server_extension(),
{
    ServerCertTypeServerExtensionCombinator(Mapped { inner: certificate_type(), mapper: ServerCertTypeServerExtensionMapper })
}
 

pub closed spec fn spec_opaque_2_ffff() -> SpecOpaque2FfffCombinator {
    SpecOpaque2FfffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: spec_uint_2_ffff(),
            snd: |deps| spec_opaque2_ffff_cont(deps),
        },
        mapper: Opaque2FfffMapper,
    }
)
}

pub open spec fn spec_opaque2_ffff_cont(deps: SpecUint2Ffff) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_2_ffff() -> (o: Opaque2FfffCombinator)
    ensures o@ == spec_opaque_2_ffff(),
{
    Opaque2FfffCombinator(
    Mapped {
        inner: Depend {
            fst: uint_2_ffff(),
            snd: Opaque2FfffCont,
            spec_snd: Ghost(|deps| spec_opaque2_ffff_cont(deps)),
        },
        mapper: Opaque2FfffMapper,
    }
)
}

impl Continuation<Uint2Ffff> for Opaque2FfffCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: Uint2Ffff) -> bool {
        true
    }

    open spec fn ensures(&self, deps: Uint2Ffff, o: Self::Output) -> bool {
        o@ == spec_opaque2_ffff_cont(deps@)
    }

    fn apply(&self, deps: Uint2Ffff) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

pub closed spec fn spec_ocsp_response() -> SpecOcspResponseCombinator {
    SpecOcspResponseCombinator(spec_opaque_1_ffffff())
}
 
pub fn ocsp_response() -> (o: OcspResponseCombinator)
    ensures o@ == spec_ocsp_response(),
{
    OcspResponseCombinator(opaque_1_ffffff())
}
 

pub closed spec fn spec_certificate_status() -> SpecCertificateStatusCombinator {
    SpecCertificateStatusCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, spec_ocsp_response()), mapper: CertificateStatusMapper })
}
 
pub fn certificate_status() -> (o: CertificateStatusCombinator)
    ensures o@ == spec_certificate_status(),
{
    CertificateStatusCombinator(Mapped { inner: (Refined { inner: U8, predicate: TagPred(CERTIFICATESTATUS_STATUS_TYPE) }, ocsp_response()), mapper: CertificateStatusMapper })
}
 

pub closed spec fn spec_heartbeat_extension() -> SpecHeartbeatExtensionCombinator {
    SpecHeartbeatExtensionCombinator(Mapped { inner: spec_heartbeat_mode(), mapper: HeartbeatExtensionMapper })
}
 
pub fn heartbeat_extension() -> (o: HeartbeatExtensionCombinator)
    ensures o@ == spec_heartbeat_extension(),
{
    HeartbeatExtensionCombinator(Mapped { inner: heartbeat_mode(), mapper: HeartbeatExtensionMapper })
}
 

pub closed spec fn spec_alert_level() -> SpecAlertLevelCombinator {
    SpecAlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}
 
pub fn alert_level() -> (o: AlertLevelCombinator)
    ensures o@ == spec_alert_level(),
{
    AlertLevelCombinator(TryMap { inner: U8, mapper: AlertLevelMapper })
}
 

pub closed spec fn spec_unknown_extension() -> SpecUnknownExtensionCombinator {
    SpecUnknownExtensionCombinator(spec_opaque_0_ffff())
}
 
pub fn unknown_extension() -> (o: UnknownExtensionCombinator)
    ensures o@ == spec_unknown_extension(),
{
    UnknownExtensionCombinator(opaque_0_ffff())
}
 

pub closed spec fn spec_alert_description() -> SpecAlertDescriptionCombinator {
    SpecAlertDescriptionCombinator(TryMap { inner: U8, mapper: AlertDescriptionMapper })
}
 
pub fn alert_description() -> (o: AlertDescriptionCombinator)
    ensures o@ == spec_alert_description(),
{
    AlertDescriptionCombinator(TryMap { inner: U8, mapper: AlertDescriptionMapper })
}
 

pub closed spec fn spec_alert() -> SpecAlertCombinator {
    SpecAlertCombinator(Mapped { inner: (spec_alert_level(), spec_alert_description()), mapper: AlertMapper })
}
 
pub fn alert() -> (o: AlertCombinator)
    ensures o@ == spec_alert(),
{
    AlertCombinator(Mapped { inner: (alert_level(), alert_description()), mapper: AlertMapper })
}
 

pub closed spec fn spec_client_cert_type_server_extension() -> SpecClientCertTypeServerExtensionCombinator {
    SpecClientCertTypeServerExtensionCombinator(Mapped { inner: spec_certificate_type(), mapper: ClientCertTypeServerExtensionMapper })
}
 
pub fn client_cert_type_server_extension() -> (o: ClientCertTypeServerExtensionCombinator)
    ensures o@ == spec_client_cert_type_server_extension(),
{
    ClientCertTypeServerExtensionCombinator(Mapped { inner: certificate_type(), mapper: ClientCertTypeServerExtensionMapper })
}
 

pub closed spec fn spec_tls_ciphertext() -> SpecTlsCiphertextCombinator {
    SpecTlsCiphertextCombinator(Mapped { inner: (spec_content_type(), (spec_protocol_version(), spec_opaque_0_ffff())), mapper: TlsCiphertextMapper })
}
 
pub fn tls_ciphertext() -> (o: TlsCiphertextCombinator)
    ensures o@ == spec_tls_ciphertext(),
{
    TlsCiphertextCombinator(Mapped { inner: (content_type(), (protocol_version(), opaque_0_ffff())), mapper: TlsCiphertextMapper })
}
 

pub closed spec fn spec_opaque_0_ffffff() -> SpecOpaque0FfffffCombinator {
    SpecOpaque0FfffffCombinator(
    Mapped {
        inner: SpecDepend {
            fst: U24Be,
            snd: |deps| spec_opaque0_ffffff_cont(deps),
        },
        mapper: Opaque0FfffffMapper,
    }
)
}

pub open spec fn spec_opaque0_ffffff_cont(deps: u24) -> Bytes {
    let l = deps;
    Bytes(l.spec_into())
}
 
pub fn opaque_0_ffffff() -> (o: Opaque0FfffffCombinator)
    ensures o@ == spec_opaque_0_ffffff(),
{
    Opaque0FfffffCombinator(
    Mapped {
        inner: Depend {
            fst: U24Be,
            snd: Opaque0FfffffCont,
            spec_snd: Ghost(|deps| spec_opaque0_ffffff_cont(deps)),
        },
        mapper: Opaque0FfffffMapper,
    }
)
}

impl Continuation<u24> for Opaque0FfffffCont {
    type Output = Bytes;

    open spec fn requires(&self, deps: u24) -> bool {
        true
    }

    open spec fn ensures(&self, deps: u24, o: Self::Output) -> bool {
        o@ == spec_opaque0_ffffff_cont(deps@)
    }

    fn apply(&self, deps: u24) -> Self::Output {
        let l = deps;
        Bytes(l.ex_into())
    }
}
 

}
