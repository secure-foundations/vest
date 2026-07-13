//! Convenient notation-style aliases for universal formats with DER encoding.
use super::{
    BitStringFmt, BmpString, Bool, Class, Explicit, GeneralizedTime, Ia5String, Implicit, Integer,
    Integer16, Integer8, Null, OctetString, PrintableString, TagFmt, TeletexString, UtcTime,
    Utf8String, ASN1, DER,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub type ASN1Bool<const DER: bool> = ASN1<Bool<DER>, DER>;

pub type ASN1Integer<const DER: bool> = ASN1<Integer, DER>;

pub type ASN1Integer8<const DER: bool> = ASN1<Integer8, DER>;

pub type ASN1Integer16<const DER: bool> = ASN1<Integer16, DER>;

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

pub const INTEGER8: ASN1Integer8<DER> = ASN1::<Integer8, DER>(TagFmt::INTEGER, Integer8);

pub const INTEGER16: ASN1Integer16<DER> = ASN1::<Integer16, DER>(TagFmt::INTEGER, Integer16);

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

/// Apply an ASN.1 context-specific IMPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn IMPLICIT<C>(number: u64, inner: ASN1<C, DER>) -> ASN1<C, DER>
    returns
        Implicit(Class::ContextSpecific, number, inner),
{
    Implicit(Class::ContextSpecific, number, inner)
}

/// Apply an ASN.1 context-specific EXPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn EXPLICIT<C>(number: u64, inner: ASN1<C, DER>) -> ASN1<ASN1<C, DER>, DER>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
}

/// The `DEFAULT` modifier for DER-encoded formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn DEFAULT<Field, Rest>(field: Field, default: Field::T, cont: Rest) -> super::Defaulted<
    Field,
    Field::T,
    Rest,
    DER,
> where Field: SpecByteLen
    returns
        super::Defaulted::<Field, Field::T, Rest, DER>(field, default, cont),
{
    super::Defaulted::<Field, Field::T, Rest, DER>(field, default, cont)
}

/// The `OPTIONAL` modifier for DER-encoded formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn OPTIONAL<Field, Rest>(field: Field, cont: Rest) -> crate::combinators::Optional<Field, Rest>
    returns
        crate::combinators::Optional::<Field, Rest>(field, cont),
{
    crate::combinators::Optional::<Field, Rest>(field, cont)
}

/// An alias for `Pair`, which makes naming more coherent with `DEFAULT` and `OPTIONAL`.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn REQUIRED<Field, Rest>(field: Field, cont: Rest) -> crate::combinators::Pair<Field, Rest>
    returns
        crate::combinators::Pair::<Field, Rest>(field, cont),
{
    crate::combinators::Pair::<Field, Rest>(field, cont)
}

/// An alias for `Choice`, which makes naming more coherent with the rest of ASN.1 combinators.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn CHOICE<A, B>(a: A, b: B) -> crate::combinators::Choice<A, B>
    returns
        crate::combinators::Choice::<A, B>(a, b),
{
    crate::combinators::Choice::<A, B>(a, b)
}

} // verus!
verus! {

proof fn chain_of_optional_defaulted() {
    use crate::combinators::*;
    use super::IntVal;
    use super::{DER, BER};
    use super::modifiers::Defaulted;
    use crate::combinators::disjoint::disjointness_lemmas;
    use super::modifiers::{lemma_disjoint_asn1_tags, lemma_disjoint_defaulted};

    broadcast use disjointness_lemmas;
    broadcast use {lemma_disjoint_asn1_tags, lemma_disjoint_defaulted};

    #[verusfmt::skip]
    let fmt =
        REQUIRED (INTEGER,
        DEFAULT  (BOOLEAN, false,
        REQUIRED (BIT_STRING,
        OPTIONAL (OCTET_STRING,
        DEFAULT  (INTEGER8, 0,
        OPTIONAL (UTC_TIME, UTF8_STRING))))));

    assert(fmt.safe_inv());
    assert(fmt.sound_inv());
    assert(fmt.unambiguous());

    #[verusfmt::skip]
    let fmt1 =
        REQUIRED  (INTEGER,
        DEFAULT   (EXPLICIT (0, INTEGER16), 10,
        OPTIONAL  (IMPLICIT (1, INTEGER16),
        OPTIONAL  (IMPLICIT (2, INTEGER16),
        DEFAULT   (EXPLICIT (3, INTEGER16), 0,
        OPTIONAL  (UTC_TIME, UTF8_STRING))))));

    assert(fmt1.safe_inv());
    assert(fmt1.sound_inv());
    assert(fmt1.unambiguous());

    #[verusfmt::skip]
    let fmt2 = CHOICE(
        IMPLICIT (0, NULL),     CHOICE(
        IMPLICIT (1, NULL),     CHOICE(
        IMPLICIT (2, INTEGER8), CHOICE(
        EXPLICIT (3, INTEGER8), CHOICE(
        OCTET_STRING, UTF8_STRING)))));

    assert(fmt2.safe_inv());
    assert(fmt2.sound_inv());
    assert(fmt2.unambiguous());
}

} // verus!
