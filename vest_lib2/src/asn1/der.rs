//! DER universal formats and notation-style aliases.
use super::modifiers::{defaulted, explicit_tag};
pub use super::modifiers::{
    implicitly_tagged as Implicit, ImplicitFmt, CHOICE, IMPLICIT, IMPLICIT_APPLICATION,
    IMPLICIT_PRIVATE, OPTIONAL, REQUIRED,
};
use super::{
    ASN1Fmt, AnyFmt, BitStringFmt, BmpStringFmt, BoolFmt, Class, EnumeratedFmt, GeneralizedTimeFmt,
    Ia5StringFmt, Integer16Fmt, Integer8Fmt, IntegerFmt, NullFmt, ObjectIdentifierFmt,
    OctetStringFmt, PrintableStringFmt, RealFmt, SetOfFmt, TagFmt, TeletexStringFmt, UtcTimeFmt,
    Utf8StringFmt, DER,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Uniform notation aliases used by schema generators.
pub type BoolTlvFmt = ASN1Fmt<BoolFmt<DER>, DER>;

pub type AnyTlvFmt = AnyFmt<DER>;

pub type IntegerTlvFmt = ASN1Fmt<IntegerFmt, DER>;

pub type Integer8TlvFmt = ASN1Fmt<Integer8Fmt, DER>;

pub type Integer16TlvFmt = ASN1Fmt<Integer16Fmt, DER>;

pub type EnumeratedTlvFmt = ASN1Fmt<EnumeratedFmt, DER>;

pub type ObjectIdentifierTlvFmt = ASN1Fmt<ObjectIdentifierFmt, DER>;

pub type RealTlvFmt = ASN1Fmt<RealFmt, DER>;

pub type BitStringTlvFmt = ASN1Fmt<BitStringFmt<DER>, DER>;

pub type OctetStringTlvFmt = ASN1Fmt<OctetStringFmt, DER>;

pub type NullTlvFmt = ASN1Fmt<NullFmt, DER>;

pub type Utf8StringTlvFmt = ASN1Fmt<Utf8StringFmt, DER>;

pub type PrintableStringTlvFmt = ASN1Fmt<PrintableStringFmt, DER>;

pub type TeletexStringTlvFmt = ASN1Fmt<TeletexStringFmt, DER>;

pub type Ia5StringTlvFmt = ASN1Fmt<Ia5StringFmt, DER>;

pub type UtcTimeTlvFmt = ASN1Fmt<UtcTimeFmt<DER>, DER>;

pub type GeneralizedTimeTlvFmt = ASN1Fmt<GeneralizedTimeFmt<DER>, DER>;

pub type BmpStringTlvFmt = ASN1Fmt<BmpStringFmt, DER>;

pub type SequenceFmt<C> = ASN1Fmt<C, DER>;

pub type SequenceOfFmt<C> = ASN1Fmt<crate::combinators::RepeatTillEnd<C>, DER>;

pub type SetOfTlvFmt<C> = ASN1Fmt<SetOfFmt<C>, DER>;

pub type ExplicitFmt<C> = ASN1Fmt<C, DER>;

pub type DefaultFmt<Field, Default, Rest> = super::DefaultedFmt<Field, Default, Rest, DER>;

pub type Eof = crate::combinators::Eof;

#[allow(non_upper_case_globals)]
pub const Eof: Eof = crate::combinators::Eof;

pub const BOOLEAN: BoolTlvFmt = ASN1Fmt(TagFmt::BOOLEAN, BoolFmt::<DER>);

pub const ANY: AnyTlvFmt = AnyFmt::<DER>;

pub const INTEGER: IntegerTlvFmt = ASN1Fmt(TagFmt::INTEGER, IntegerFmt);

pub const INTEGER8: Integer8TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer8Fmt);

pub const INTEGER16: Integer16TlvFmt = ASN1Fmt(TagFmt::INTEGER, Integer16Fmt);

pub const ENUMERATED: EnumeratedTlvFmt = ASN1Fmt(TagFmt::ENUMERATED, EnumeratedFmt);

pub const OBJECT_IDENTIFIER: ObjectIdentifierTlvFmt = ASN1Fmt(
    TagFmt::OBJECT_IDENTIFIER,
    ObjectIdentifierFmt,
);

pub const REAL: RealTlvFmt = ASN1Fmt(TagFmt::REAL, RealFmt);

pub const BIT_STRING: BitStringTlvFmt = ASN1Fmt(TagFmt::BIT_STRING, BitStringFmt::<DER>);

pub const OCTET_STRING: OctetStringTlvFmt = ASN1Fmt(TagFmt::OCTET_STRING, OctetStringFmt);

pub const NULL: NullTlvFmt = ASN1Fmt(TagFmt::NULL, NullFmt);

pub const UTF8_STRING: Utf8StringTlvFmt = ASN1Fmt(TagFmt::UTF8_STRING, Utf8StringFmt);

pub const PRINTABLE_STRING: PrintableStringTlvFmt = ASN1Fmt(
    TagFmt::PRINTABLE_STRING,
    PrintableStringFmt,
);

pub const TELETEX_STRING: TeletexStringTlvFmt = ASN1Fmt(TagFmt::TELETEX_STRING, TeletexStringFmt);

pub const IA5_STRING: Ia5StringTlvFmt = ASN1Fmt(TagFmt::IA5_STRING, Ia5StringFmt);

pub const UTC_TIME: UtcTimeTlvFmt = ASN1Fmt(TagFmt::UTC_TIME, UtcTimeFmt::<DER>);

pub const GENERALIZED_TIME: GeneralizedTimeTlvFmt = ASN1Fmt(
    TagFmt::GENERALIZED_TIME,
    GeneralizedTimeFmt::<DER>,
);

pub const BMP_STRING: BmpStringTlvFmt = ASN1Fmt(TagFmt::BMP_STRING, BmpStringFmt);

/// Construct a DER `SET OF` whose elements are complete DER formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SET_OF<C: Copy>(inner: C) -> SetOfTlvFmt<C>
    returns
        ASN1Fmt::<SetOfFmt<C>, DER>(TagFmt::SET, SetOfFmt(inner)),
{
    ASN1Fmt::<SetOfFmt<C>, DER>(TagFmt::SET, SetOfFmt(inner))
}

/// Construct a DER `SEQUENCE` format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE<C: Copy>(inner: C) -> SequenceFmt<C>
    returns
        ASN1Fmt::<C, DER>(TagFmt::SEQUENCE, inner),
{
    ASN1Fmt::<C, DER>(TagFmt::SEQUENCE, inner)
}

/// Construct a DER `SEQUENCE OF` whose elements are complete DER formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn SEQUENCE_OF<C: Copy>(inner: C) -> SequenceOfFmt<C>
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

/// Apply an ASN.1 EXPLICIT tag with an arbitrary tag class.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn Explicit<C: Copy>(class: Class, number: u64, inner: C) -> ExplicitFmt<C>
    returns
        ASN1Fmt::<C, DER>(explicit_tag(class, number), inner),
{
    ASN1Fmt(explicit_tag(class, number), inner)
}

/// Apply an ASN.1 context-specific EXPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
}

/// Apply an ASN.1 application-class EXPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_APPLICATION<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Application, number, inner),
{
    Explicit(Class::Application, number, inner)
}

/// Apply an ASN.1 private-class EXPLICIT tag to a DER-encoded format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn EXPLICIT_PRIVATE<C: Copy>(number: u64, inner: C) -> ExplicitFmt<C>
    returns
        Explicit(Class::Private, number, inner),
{
    Explicit(Class::Private, number, inner)
}

/// The `DEFAULT` modifier for DER-encoded formats.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn DEFAULT<Field, Rest>(field: Field, default: Field::T, cont: Rest) -> DefaultFmt<
    Field,
    Field::T,
    Rest,
> where Field: SpecByteLen
    returns
        defaulted::<Field, Rest, DER>(field, default, cont),
{
    defaulted::<Field, Rest, DER>(field, default, cont)
}

} // verus!
verus! {

use crate::combinators::{Choice, Optional, Pair};

#[verifier::allow_in_spec]
#[allow(non_snake_case)]
const fn MY_FMT() -> Pair<
    IntegerTlvFmt,
    DefaultFmt<
        BoolTlvFmt,
        bool,
        Pair<
            BitStringTlvFmt,
            Optional<
                OctetStringTlvFmt,
                DefaultFmt<Integer8TlvFmt, i8, Optional<UtcTimeTlvFmt, Utf8StringTlvFmt>>,
            >,
        >,
    >,
>
    returns
        REQUIRED(
            INTEGER,
            DEFAULT(
                BOOLEAN,
                false,
                REQUIRED(
                    BIT_STRING,
                    OPTIONAL(OCTET_STRING, DEFAULT(INTEGER8, 0, OPTIONAL(UTC_TIME, UTF8_STRING))),
                ),
            ),
        ),
{
    REQUIRED(
        INTEGER,
        DEFAULT(
            BOOLEAN,
            false,
            REQUIRED(
                BIT_STRING,
                OPTIONAL(OCTET_STRING, DEFAULT(INTEGER8, 0, OPTIONAL(UTC_TIME, UTF8_STRING))),
            ),
        ),
    )
}

#[verifier::allow_in_spec]
#[allow(non_snake_case)]
const fn MY_FMT2() -> Pair<
    IntegerTlvFmt,
    DefaultFmt<
        ExplicitFmt<Integer16TlvFmt>,
        i16,
        Optional<
            ImplicitFmt<Integer16TlvFmt>,
            Optional<
                ImplicitFmt<Integer16TlvFmt>,
                DefaultFmt<
                    ExplicitFmt<Integer16TlvFmt>,
                    i16,
                    Optional<UtcTimeTlvFmt, Utf8StringTlvFmt>,
                >,
            >,
        >,
    >,
>
    returns
        REQUIRED(
            INTEGER,
            DEFAULT(
                EXPLICIT(0, INTEGER16),
                10,
                OPTIONAL(
                    IMPLICIT(1, INTEGER16),
                    OPTIONAL(
                        IMPLICIT(2, INTEGER16),
                        DEFAULT(EXPLICIT(3, INTEGER16), 0, OPTIONAL(UTC_TIME, UTF8_STRING)),
                    ),
                ),
            ),
        ),
{
    REQUIRED(
        INTEGER,
        DEFAULT(
            EXPLICIT(0, INTEGER16),
            10,
            OPTIONAL(
                IMPLICIT(1, INTEGER16),
                OPTIONAL(
                    IMPLICIT(2, INTEGER16),
                    DEFAULT(EXPLICIT(3, INTEGER16), 0, OPTIONAL(UTC_TIME, UTF8_STRING)),
                ),
            ),
        ),
    )
}

proof fn chain_of_optional_defaulted() {
    use crate::combinators::disjoint::disjointness_lemmas;
    use super::disjoint::asn1_disjointness_lemmas;

    broadcast use disjointness_lemmas;
    broadcast use asn1_disjointness_lemmas;

    assert(MY_FMT().safe_inv());
    assert(MY_FMT().sound_inv());
    assert(MY_FMT().unambiguous());
    assert(MY_FMT().nonmal_inv());

    assert(MY_FMT2().safe_inv());
    assert(MY_FMT2().sound_inv());
    assert(MY_FMT2().unambiguous());
    assert(MY_FMT2().nonmal_inv());

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
