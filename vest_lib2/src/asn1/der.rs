//! Convenient notation-style aliases for universal formats with DER encoding.
use super::{
    ASN1Fmt, AnyFmt, BitStringFmt, BmpStringFmt, BoolFmt, Class, EnumeratedFmt, Explicit,
    GeneralizedTimeFmt, Ia5StringFmt, Implicit, Integer16Fmt, Integer8Fmt, IntegerFmt, NullFmt,
    ObjectIdentifierFmt, OctetStringFmt, PrintableStringFmt, RealFmt, SetOfFmt, TagFmt,
    TeletexStringFmt, UtcTimeFmt, Utf8StringFmt, DER,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub type ASN1BoolFmt<const DER: bool> = ASN1Fmt<BoolFmt<DER>, DER>;

pub type ASN1AnyFmt<const DER: bool> = AnyFmt<DER>;

pub type ASN1IntegerFmt<const DER: bool> = ASN1Fmt<IntegerFmt, DER>;

pub type ASN1Integer8Fmt<const DER: bool> = ASN1Fmt<Integer8Fmt, DER>;

pub type ASN1Integer16Fmt<const DER: bool> = ASN1Fmt<Integer16Fmt, DER>;

pub type ASN1EnumeratedFmt<const DER: bool> = ASN1Fmt<EnumeratedFmt, DER>;

pub type ASN1ObjectIdentifierFmt<const DER: bool> = ASN1Fmt<ObjectIdentifierFmt, DER>;

pub type ASN1RealFmt<const DER: bool> = ASN1Fmt<RealFmt, DER>;

pub type ASN1BitStringFmt<const DER: bool> = ASN1Fmt<BitStringFmt<DER>, DER>;

pub type ASN1OctetStringFmt<const DER: bool> = ASN1Fmt<OctetStringFmt, DER>;

pub type ASN1NullFmt<const DER: bool> = ASN1Fmt<NullFmt, DER>;

pub type ASN1Utf8StringFmt<const DER: bool> = ASN1Fmt<Utf8StringFmt, DER>;

pub type ASN1PrintableStringFmt<const DER: bool> = ASN1Fmt<PrintableStringFmt, DER>;

pub type ASN1TeletexStringFmt<const DER: bool> = ASN1Fmt<TeletexStringFmt, DER>;

pub type ASN1Ia5StringFmt<const DER: bool> = ASN1Fmt<Ia5StringFmt, DER>;

pub type ASN1UtcTimeFmt<const DER: bool> = ASN1Fmt<UtcTimeFmt<DER>, DER>;

pub type ASN1GeneralizedTimeFmt<const DER: bool> = ASN1Fmt<GeneralizedTimeFmt<DER>, DER>;

pub type ASN1BmpStringFmt<const DER: bool> = ASN1Fmt<BmpStringFmt, DER>;

pub type ASN1SetOfFmt<C> = ASN1Fmt<SetOfFmt<C>, DER>;

pub type ASN1SequenceOfFmt<C> = ASN1Fmt<crate::combinators::RepeatTillEnd<C>, DER>;

pub const BOOLEAN: ASN1BoolFmt<DER> = ASN1Fmt::<BoolFmt<DER>, DER>(TagFmt::BOOLEAN, BoolFmt::<DER>);

pub const ANY: ASN1AnyFmt<DER> = AnyFmt::<DER>;

pub const INTEGER: ASN1IntegerFmt<DER> = ASN1Fmt::<IntegerFmt, DER>(TagFmt::INTEGER, IntegerFmt);

pub const INTEGER8: ASN1Integer8Fmt<DER> = ASN1Fmt::<Integer8Fmt, DER>(
    TagFmt::INTEGER,
    Integer8Fmt,
);

pub const INTEGER16: ASN1Integer16Fmt<DER> = ASN1Fmt::<Integer16Fmt, DER>(
    TagFmt::INTEGER,
    Integer16Fmt,
);

pub const ENUMERATED: ASN1EnumeratedFmt<DER> = ASN1Fmt::<EnumeratedFmt, DER>(
    TagFmt::ENUMERATED,
    EnumeratedFmt,
);

pub const OBJECT_IDENTIFIER: ASN1ObjectIdentifierFmt<DER> = ASN1Fmt::<ObjectIdentifierFmt, DER>(
    TagFmt::OBJECT_IDENTIFIER,
    ObjectIdentifierFmt,
);

pub const REAL: ASN1RealFmt<DER> = ASN1Fmt::<RealFmt, DER>(TagFmt::REAL, RealFmt);

pub const BIT_STRING: ASN1BitStringFmt<DER> = ASN1Fmt::<BitStringFmt<DER>, DER>(
    TagFmt::BIT_STRING,
    BitStringFmt::<DER>,
);

pub const OCTET_STRING: ASN1OctetStringFmt<DER> = ASN1Fmt::<OctetStringFmt, DER>(
    TagFmt::OCTET_STRING,
    OctetStringFmt,
);

pub const NULL: ASN1NullFmt<DER> = ASN1Fmt::<NullFmt, DER>(TagFmt::NULL, NullFmt);

pub const UTF8_STRING: ASN1Utf8StringFmt<DER> = ASN1Fmt::<Utf8StringFmt, DER>(
    TagFmt::UTF8_STRING,
    Utf8StringFmt,
);

pub const PRINTABLE_STRING: ASN1PrintableStringFmt<DER> = ASN1Fmt::<PrintableStringFmt, DER>(
    TagFmt::PRINTABLE_STRING,
    PrintableStringFmt,
);

pub const TELETEX_STRING: ASN1TeletexStringFmt<DER> = ASN1Fmt::<TeletexStringFmt, DER>(
    TagFmt::TELETEX_STRING,
    TeletexStringFmt,
);

pub const IA5_STRING: ASN1Ia5StringFmt<DER> = ASN1Fmt::<Ia5StringFmt, DER>(
    TagFmt::IA5_STRING,
    Ia5StringFmt,
);

pub const UTC_TIME: ASN1UtcTimeFmt<DER> = ASN1Fmt::<UtcTimeFmt<DER>, DER>(
    TagFmt::UTC_TIME,
    UtcTimeFmt::<DER>,
);

pub const GENERALIZED_TIME: ASN1GeneralizedTimeFmt<DER> = ASN1Fmt::<GeneralizedTimeFmt<DER>, DER>(
    TagFmt::GENERALIZED_TIME,
    GeneralizedTimeFmt::<DER>,
);

pub const BMP_STRING: ASN1BmpStringFmt<DER> = ASN1Fmt::<BmpStringFmt, DER>(
    TagFmt::BMP_STRING,
    BmpStringFmt,
);

/// Construct a DER `SET OF` whose elements are complete DER formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn SET_OF<C>(inner: C) -> ASN1SetOfFmt<C>
    returns
        ASN1Fmt::<SetOfFmt<C>, DER>(TagFmt::SET, SetOfFmt(inner)),
{
    ASN1Fmt::<SetOfFmt<C>, DER>(TagFmt::SET, SetOfFmt(inner))
}

/// Construct a DER `SEQUENCE OF` whose elements are complete DER formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn SEQUENCE_OF<C>(inner: C) -> ASN1SequenceOfFmt<C>
    returns
        ASN1Fmt::<crate::combinators::RepeatTillEnd<C>, DER>(
            TagFmt::SEQUENCE,
            crate::combinators::RepeatTillEnd(inner),
        ),
{
    ASN1Fmt::<crate::combinators::RepeatTillEnd<C>, DER>(
        TagFmt::SEQUENCE,
        crate::combinators::RepeatTillEnd(inner),
    )
}

/// Apply an ASN.1 context-specific IMPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn IMPLICIT<C>(number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<C, DER>
    returns
        Implicit(Class::ContextSpecific, number, inner),
{
    Implicit(Class::ContextSpecific, number, inner)
}

/// Apply an ASN.1 context-specific EXPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn EXPLICIT<C>(number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<ASN1Fmt<C, DER>, DER>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
}

/// The `DEFAULT` modifier for DER-encoded formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn DEFAULT<Field, Rest>(field: Field, default: Field::T, cont: Rest) -> super::DefaultedFmt<
    Field,
    Field::T,
    Rest,
    DER,
> where Field: SpecByteLen
    returns
        super::DefaultedFmt::<Field, Field::T, Rest, DER>(field, default, cont),
{
    super::DefaultedFmt::<Field, Field::T, Rest, DER>(field, default, cont)
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
    use super::IntegerFmt;
    use super::{DER, BER};
    use super::modifiers::DefaultedFmt;
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
