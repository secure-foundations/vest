//! Convenient notation-style aliases for universal formats with DER encoding.
use super::{
    BitStringFmt, BmpString, Bool, GeneralizedTime, Ia5String, Integer, Null, OctetString,
    PrintableString, TagFmt, TeletexString, UtcTime, Utf8String, ASN1, DER,
};
use vstd::prelude::*;

verus! {

pub type ASN1Bool<const DER: bool> = ASN1<Bool<DER>, DER>;

pub type ASN1Integer<const DER: bool> = ASN1<Integer, DER>;

pub type ASN1BitString<const DER: bool> = ASN1<BitStringFmt<DER>, DER>;

pub type ASN1OctetString<const DER: bool> = ASN1<OctetString, DER>;

pub type ASN1Null<const DER: bool> = ASN1<Null, DER>;

pub type ASN1Utf8String<const DER: bool> = ASN1<Utf8String, DER>;

pub type ASN1PrintableString<const DER: bool> = ASN1<PrintableString, DER>;

pub type ASN1TeletexString<const DER: bool> = ASN1<TeletexString, DER>;

pub type ASN1Ia5String<const DER: bool> = ASN1<Ia5String, DER>;

pub type ASN1UtcTime<const DER: bool> = ASN1<UtcTime<DER>, DER>;

pub type ASN1GeneralizedTime<const DER: bool> = ASN1<GeneralizedTime<DER>, DER>;

pub type ASN1BmpString<const DER: bool> = ASN1<BmpString, DER>;

pub const BOOLEAN: ASN1Bool<DER> = ASN1::<Bool<DER>, DER>(TagFmt::BOOLEAN, Bool::<DER>);

pub const INTEGER: ASN1Integer<DER> = ASN1::<Integer, DER>(TagFmt::INTEGER, Integer);

pub const BIT_STRING: ASN1BitString<DER> = ASN1::<BitStringFmt<DER>, DER>(
    TagFmt::BIT_STRING,
    BitStringFmt::<DER>,
);

pub const OCTET_STRING: ASN1OctetString<DER> = ASN1::<OctetString, DER>(
    TagFmt::OCTET_STRING,
    OctetString,
);

pub const NULL: ASN1Null<DER> = ASN1::<Null, DER>(TagFmt::NULL, Null);

pub const UTF8_STRING: ASN1Utf8String<DER> = ASN1::<Utf8String, DER>(
    TagFmt::UTF8_STRING,
    Utf8String,
);

pub const PRINTABLE_STRING: ASN1PrintableString<DER> = ASN1::<PrintableString, DER>(
    TagFmt::PRINTABLE_STRING,
    PrintableString,
);

pub const TELETEX_STRING: ASN1TeletexString<DER> = ASN1::<TeletexString, DER>(
    TagFmt::TELETEX_STRING,
    TeletexString,
);

pub const IA5_STRING: ASN1Ia5String<DER> = ASN1::<Ia5String, DER>(TagFmt::IA5_STRING, Ia5String);

pub const UTC_TIME: ASN1UtcTime<DER> = ASN1::<UtcTime<DER>, DER>(TagFmt::UTC_TIME, UtcTime::<DER>);

pub const GENERALIZED_TIME: ASN1GeneralizedTime<DER> = ASN1::<GeneralizedTime<DER>, DER>(
    TagFmt::GENERALIZED_TIME,
    GeneralizedTime::<DER>,
);

pub const BMP_STRING: ASN1BmpString<DER> = ASN1::<BmpString, DER>(TagFmt::BMP_STRING, BmpString);

} // verus!
