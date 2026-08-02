//! Shared ASN.1 component modifiers and notation constructors.
use crate::asn1::ber::{
    BerBitStringFmt, BerCharStringFmt, BerOctetStringFmt, BerSequenceFmt, BerSequenceOfFmt,
};
use crate::asn1::tag::Class;
use crate::asn1::{ASN1Fmt, Tag};
use crate::combinators::mapped::spec::{FnSpecMapper, SpecMapper};
use crate::combinators::{Choice, Mapped, Optional, Pair, Ref, Refined};
use crate::core::exec::output::*;
use crate::core::exec::{
    input::{InputBuf, InputSlice},
    parser::{PResult, Parser},
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;
use OutputBuf;

verus! {

/// Formats whose outer ASN.1 tag can be replaced without changing their semantic value.
///
/// The replacement's class and number are authoritative; each format determines the
/// primitive/constructed bit required by its own wire representation.
pub trait Retaggable: Copy {
    spec fn spec_retagged(&self, tag: Tag) -> Self;

    fn retagged(&self, tag: Tag) -> (retagged: Self)
        returns
            self.spec_retagged(tag),
    ;
}

/// Const-constructible ASN.1 IMPLICIT tagging wrapper.
#[derive(Copy)]
pub struct ImplicitlyTaggedFmt<F>(pub Tag, pub F);

impl<F: Clone> Clone for ImplicitlyTaggedFmt<F> {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.0 == self.0,
            call_ensures(F::clone, (&self.1,), cloned.1),
    {
        Self(self.0, self.1.clone())
    }
}

/// Supports IMPLICIT tagging of an ordinary ASN.1 TLV.
///
/// Retagging replaces the tag class and number, preserves the base format's primitive/constructed
/// form, and leaves its content format unchanged.
impl<C: Copy, const DER: bool> Retaggable for ASN1Fmt<C, DER> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        ASN1Fmt(
            Tag { class: tag.class, constructed: self.0.constructed, number: tag.number },
            self.1,
        )
    }

    fn retagged(&self, tag: Tag) -> Self {
        ASN1Fmt(
            Tag { class: tag.class, constructed: self.0.constructed, number: tag.number },
            self.1,
        )
    }
}

/// Supports IMPLICIT tagging of a BER `SEQUENCE` or EXPLICIT wrapper without losing its
/// definite/indefinite-length framing.
///
/// Retagging replaces the tag class and number, forces the required constructed form, and
/// preserves the schema-defined content format.
impl<C: Copy> Retaggable for BerSequenceFmt<C> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: true, number: tag.number }, self.1)
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: true, number: tag.number }, self.1)
    }
}

/// Supports IMPLICIT tagging of a BER `SEQUENCE OF`/`SET OF` while retaining its specialized
/// definite/indefinite-length handling.
///
/// Retagging replaces the tag class and number, forces the required constructed form, and
/// preserves the element format.
impl<C: Copy> Retaggable for BerSequenceOfFmt<C> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: true, number: tag.number }, self.1)
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: true, number: tag.number }, self.1)
    }
}

/// Supports IMPLICIT tagging of recursive BER OCTET STRING values.
///
/// The stored tag is normalized to the primitive form with the replacement class and number; this
/// is fine since the parser permits both primitive and constructed forms.
/// Recursive fragments keep universal tag 4 (see [`BerOctetStringFmt`]).
impl<const LIMIT: usize> Retaggable for BerOctetStringFmt<LIMIT> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number })
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number })
    }
}

/// Supports IMPLICIT tagging of recursive BER BIT STRING values.
///
/// The outer identity is replaced and normalized to primitive form; parsing still accepts both
/// primitive and constructed forms, while nested fragments retain universal tag 3.
impl<const LIMIT: usize> Retaggable for BerBitStringFmt<LIMIT> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number })
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number })
    }
}

/// Supports IMPLICIT tagging of a BER restricted character string layered over OCTET STRING.
///
/// The outer tag is normalized to the primitive form with the replacement class and number,
/// while OCTET STRING fragment tags, the character-content format, and the recursion limit are
/// preserved.
impl<C: Copy, const LIMIT: usize> Retaggable for BerCharStringFmt<C, LIMIT> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number }, self.1)
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(Tag { class: tag.class, constructed: false, number: tag.number }, self.1)
    }
}

/// Allows IMPLICIT tagging to compose/chain through an existing IMPLICIT-tag wrapper.
///
/// The newer tag replaces the stored outer tag and the underlying format is retained; when used,
/// the underlying [`Retaggable`] implementation selects the correct primitive/constructed form.
impl<F: Retaggable> Retaggable for ImplicitlyTaggedFmt<F> {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Self(tag, self.1)
    }

    fn retagged(&self, tag: Tag) -> Self {
        Self(tag, self.1)
    }
}

/// Allows a value constraint to remain attached when its underlying ASN.1 format is retagged.
///
/// Retagging is delegated to the inner format and the refinement predicate is preserved.
impl<F, P> Retaggable for Refined<F, P> where F: Retaggable, P: Copy {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Refined(self.0.spec_retagged(tag), self.1)
    }

    fn retagged(&self, tag: Tag) -> Self {
        Refined(self.0.retagged(tag), self.1)
    }
}

/// Allows a semantic mapping to remain attached when its underlying ASN.1 format is retagged.
///
/// Retagging is delegated to the inner format and the mapper is preserved.
impl<F, M> Retaggable for Mapped<F, M> where F: Retaggable, M: Copy {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Mapped { inner: self.inner.spec_retagged(tag), mapper: self.mapper }
    }

    fn retagged(&self, tag: Tag) -> Self {
        Mapped { inner: self.inner.retagged(tag), mapper: self.mapper }
    }
}

/// Allows references to retaggable formats to pass transparently through IMPLICIT tagging.
///
/// Retagging is delegated to the referenced format and the result remains wrapped in [`Ref`].
impl<F> Retaggable for Ref<F> where F: Retaggable {
    open spec fn spec_retagged(&self, tag: Tag) -> Self {
        Ref(self.0.spec_retagged(tag))
    }

    fn retagged(&self, tag: Tag) -> Self {
        Ref(self.0.retagged(tag))
    }
}

mod implicit_specs {
    use super::*;

    impl<F> SpecParser for ImplicitlyTaggedFmt<F> where F: Retaggable + SpecParser {
        type PVal = <F as SpecParser>::PVal;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            self.1.spec_retagged(self.0).spec_parse(ibuf)
        }
    }

    impl<F> Consistency for ImplicitlyTaggedFmt<F> where F: Retaggable + Consistency {
        type Val = <F as Consistency>::Val;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            self.1.spec_retagged(self.0).consistent(value)
        }
    }

    impl<F> SpecSerializerDps for ImplicitlyTaggedFmt<F> where F: Retaggable + SpecSerializerDps {
        type SValue = <F as SpecSerializerDps>::SValue;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            self.1.spec_retagged(self.0).spec_serialize_dps(value, obuf)
        }
    }

    impl<F> SpecSerializer for ImplicitlyTaggedFmt<F> where F: Retaggable + SpecSerializer {
        type SVal = <F as SpecSerializer>::SVal;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            self.1.spec_retagged(self.0).spec_serialize(value)
        }
    }

    impl<F> SpecByteLen for ImplicitlyTaggedFmt<F> where F: Retaggable + SpecByteLen {
        type T = <F as SpecByteLen>::T;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            self.1.spec_retagged(self.0).byte_len(value)
        }
    }

}

mod implicit_proofs {
    use super::*;

    impl<F> SafeParser for ImplicitlyTaggedFmt<F> where F: Retaggable + SafeParser {
        open spec fn safe_inv(&self) -> bool {
            self.1.spec_retagged(self.0).safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_parse_safe(ibuf);
        }
    }

    impl<F> Productive for ImplicitlyTaggedFmt<F> where F: Retaggable + Productive {
        open spec fn productive_inv(&self) -> bool {
            self.1.spec_retagged(self.0).productive_inv()
        }

        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_productive(ibuf);
        }
    }

    impl<F> SoundParser for ImplicitlyTaggedFmt<F> where F: Retaggable + SoundParser {
        open spec fn sound_inv(&self) -> bool {
            self.1.spec_retagged(self.0).sound_inv()
        }

        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_parse_sound_value(ibuf);
        }
    }

    impl<F> NonTailFmt for ImplicitlyTaggedFmt<F> where F: Retaggable + NonTailFmt {
        open spec fn serialize_dps_inv(&self) -> bool {
            self.1.spec_retagged(self.0).serialize_dps_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<F> GoodSerializer for ImplicitlyTaggedFmt<F> where F: Retaggable + GoodSerializer {
        open spec fn serialize_inv(&self) -> bool {
            self.1.spec_retagged(self.0).serialize_inv()
        }

        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            self.1.spec_retagged(self.0).lemma_serialize_len(value);
        }
    }

    impl<F> SPRoundTripDps for ImplicitlyTaggedFmt<F> where F: Retaggable + SPRoundTripDps {
        open spec fn unambiguous(&self) -> bool {
            self.1.spec_retagged(self.0).unambiguous()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            self.1.spec_retagged(self.0).theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

    impl<F> NonMalleable for ImplicitlyTaggedFmt<F> where F: Retaggable + NonMalleable {
        open spec fn nonmal_inv(&self) -> bool {
            self.1.spec_retagged(self.0).nonmal_inv()
        }

        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<F> NoLookAhead for ImplicitlyTaggedFmt<F> where F: Retaggable + NoLookAhead {
        open spec fn no_lookahead_inv(&self) -> bool {
            self.1.spec_retagged(self.0).no_lookahead_inv()
        }

        proof fn lemma_no_lookahead(&self, ibuf1: Seq<u8>, ibuf2: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_no_lookahead(ibuf1, ibuf2);
        }
    }

    impl<F> EquivSerializersGeneral for ImplicitlyTaggedFmt<F> where
        F: Retaggable + EquivSerializersGeneral,
     {
        open spec fn equiv_general_inv(&self) -> bool {
            self.1.spec_retagged(self.0).equiv_general_inv()
        }

        proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
            self.1.spec_retagged(self.0).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<F> EquivSerializers for ImplicitlyTaggedFmt<F> where F: Retaggable + EquivSerializers {
        open spec fn equiv_inv(&self) -> bool {
            self.1.spec_retagged(self.0).equiv_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            self.1.spec_retagged(self.0).lemma_serialize_equiv_on_empty(value);
        }
    }

}

impl<Input, F> Parser<Input> for ImplicitlyTaggedFmt<F> where
    Input: InputBuf,
    F: Retaggable + Parser<Input>,
 {
    type PT = <F as Parser<Input>>::PT;

    open spec fn exec_inv(&self) -> bool {
        <F as Parser<Input>>::exec_inv(&self.1.spec_retagged(self.0))
    }

    fn parse(&self, ibuf: &Input) -> PResult<Self::PT> {
        self.1.retagged(self.0).parse(ibuf)
    }
}

impl<Output, F, T> Serializer<Output, T> for ImplicitlyTaggedFmt<F> where
    Output: OutputBuf,
    T: DeepView + ?Sized,
    F: Retaggable + Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        <F as Serializer<Output, T>>::exec_inv(&self.1.spec_retagged(self.0))
    }

    fn serialize_into(&self, value: &T, obuf: &mut Output) {
        self.1.retagged(self.0).serialize_into(value, obuf)
    }
}

impl<F, T> Prepare<T> for ImplicitlyTaggedFmt<F> where
    T: DeepView + ?Sized,
    F: Retaggable + Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        <F as Prepare<T>>::exec_inv(&self.1.spec_retagged(self.0))
    }

    fn prepare(&self, value: &T) -> Result<usize, PreSerializeError> {
        self.1.retagged(self.0).prepare(value)
    }
}

impl<F, T> ByteLen<T> for ImplicitlyTaggedFmt<F> where
    T: DeepView + ?Sized,
    F: Retaggable + ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        <F as ByteLen<T>>::exec_inv(&self.1.spec_retagged(self.0))
    }

    fn length(&self, value: &T) -> usize {
        self.1.retagged(self.0).length(value)
    }
}

/// Rule-independent format type produced by ASN.1 IMPLICIT tagging.
pub type ImplicitFmt<F> = ImplicitlyTaggedFmt<F>;

/// Apply an ASN.1 IMPLICIT tag with an arbitrary tag class.
///
/// The supplied tag's constructed bit is only a placeholder: the concrete [`Retaggable`]
/// implementation preserves or selects the encoding form required by the base format.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn implicitly_tagged<C: Copy>(class: Class, number: u64, inner: C) -> ImplicitFmt<C>
    returns
        ImplicitlyTaggedFmt(
            Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) },
            inner,
        ),
{
    ImplicitlyTaggedFmt(
        Tag { class, constructed: false, number: super::tag::tag_num_from_uint(number) },
        inner,
    )
}

/// Apply a context-specific ASN.1 IMPLICIT tag.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn IMPLICIT<C: Copy>(number: u64, inner: C) -> ImplicitFmt<C>
    returns
        implicitly_tagged(Class::ContextSpecific, number, inner),
{
    implicitly_tagged(Class::ContextSpecific, number, inner)
}

/// Apply an application-class ASN.1 IMPLICIT tag.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn IMPLICIT_APPLICATION<C: Copy>(number: u64, inner: C) -> ImplicitFmt<C>
    returns
        implicitly_tagged(Class::Application, number, inner),
{
    implicitly_tagged(Class::Application, number, inner)
}

/// Apply a private-class ASN.1 IMPLICIT tag.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn IMPLICIT_PRIVATE<C: Copy>(number: u64, inner: C) -> ImplicitFmt<C>
    returns
        implicitly_tagged(Class::Private, number, inner),
{
    implicitly_tagged(Class::Private, number, inner)
}

/// Construct an ASN.1 OPTIONAL component with its continuation.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn OPTIONAL<Field, Rest>(field: Field, rest: Rest) -> Optional<Field, Rest>
    returns
        Optional(field, rest),
{
    Optional(field, rest)
}

/// Construct a required ASN.1 component with its continuation.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn REQUIRED<Field, Rest>(field: Field, rest: Rest) -> Pair<Field, Rest>
    returns
        Pair(field, rest),
{
    Pair(field, rest)
}

/// Construct a binary ASN.1 CHOICE.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub const fn CHOICE<Left, Right>(left: Left, right: Right) -> Choice<Left, Right>
    returns
        Choice(left, right),
{
    Choice(left, right)
}

/// Construct the outer tag used by ASN.1 EXPLICIT tagging.
#[verifier::allow_in_spec]
pub const fn explicit_tag(class: Class, number: u64) -> Tag
    returns
        (Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) }),
{
    Tag { class, constructed: true, number: super::tag::tag_num_from_uint(number) }
}

/// ASN.1 DEFAULT component with continuation.
///
/// The semantic value always contains the component value. On parsing, absence
/// is replaced by `default`. On serialization, a value equal to `default` is
/// omitted. DER additionally rejects an explicitly encoded default value.
#[derive(Copy)]
pub struct DefaultedFmt<Field, Default, Rest, const DER: bool = true>(
    pub Field,
    pub Default,
    pub Rest,
);

/// Construct an ASN.1 DEFAULT component for the selected encoding rules.
#[verifier::allow_in_spec]
pub const fn defaulted<Field, Rest, const DER: bool>(
    field: Field,
    default: Field::T,
    rest: Rest,
) -> DefaultedFmt<Field, Field::T, Rest, DER> where Field: SpecByteLen
    returns
        DefaultedFmt::<Field, Field::T, Rest, DER>(field, default, rest),
{
    DefaultedFmt::<Field, Field::T, Rest, DER>(field, default, rest)
}

impl<Field: Clone, Default: Clone, Rest: Clone, const DER: bool> Clone for DefaultedFmt<
    Field,
    Default,
    Rest,
    DER,
> {
    fn clone(&self) -> (cloned: Self)
        ensures
            call_ensures(Field::clone, (&self.0,), cloned.0),
            call_ensures(Default::clone, (&self.1,), cloned.1),
            call_ensures(Rest::clone, (&self.2,), cloned.2),
    {
        DefaultedFmt(self.0.clone(), self.1.clone(), self.2.clone())
    }
}

pub type DefaultedInnerFmt<Field, Rest, T, U, const DER: bool> = Mapped<
    Refined<Optional<Field, Rest>, PredFnSpec<(Option<T>, U)>>,
    FnSpecMapper<(Option<T>, U), (T, U)>,
>;

pub open spec fn defaulted_fmt<Field: SpecByteLen, Rest: SpecByteLen, const DER: bool>(
    field: Field,
    default: Field::T,
    rest: Rest,
) -> DefaultedInnerFmt<Field, Rest, Field::T, Rest::T, DER> {
    Mapped {
        inner: Refined(
            Optional(field, rest),
            |pair: (Option<Field::T>, Rest::T)|
                DER ==> (pair matches (Some(value), _) ==> value != default),
        ),
        mapper: (
            |parsed: (Option<Field::T>, Rest::T)|
                (
                    match parsed.0 {
                        Some(value) => value,
                        None => default,
                    },
                    parsed.1,
                ),
            |value: (Field::T, Rest::T)|
                (
                    if value.0 == default {
                        None
                    } else {
                        Some(value.0)
                    },
                    value.1,
                ),
        ),
    }
}

mod derived_specs {
    use super::*;

    impl<Field, Rest, const DER: bool> SpecParser for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + SpecParser<PVal = Field::T>,
        Rest: SpecByteLen + SpecParser<PVal = Rest::T>,
     {
        type PVal = (Field::PVal, Rest::PVal);

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).spec_parse(ibuf)
        }
    }

    impl<Field, Rest, const DER: bool> Consistency for DefaultedFmt<
        Field,
        Field::Val,
        Rest,
        DER,
    > where
        Field: SpecByteLen + Consistency<Val = Field::T>,
        Rest: SpecByteLen + Consistency<Val = Rest::T>,
     {
        type Val = (Field::Val, Rest::Val);

        open spec fn consistent(&self, v: Self::Val) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).consistent(v)
        }
    }

    impl<Field, Rest, const DER: bool> SpecSerializerDps for DefaultedFmt<
        Field,
        Field::SValue,
        Rest,
        DER,
    > where
        Field: SpecByteLen + SpecSerializerDps<SValue = Field::T>,
        Rest: SpecByteLen + SpecSerializerDps<SValue = Rest::T>,
     {
        type SValue = (Field::SValue, Rest::SValue);

        open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).spec_serialize_dps(v, obuf)
        }
    }

    impl<Field, Rest, const DER: bool> SpecSerializer for DefaultedFmt<
        Field,
        Field::SVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + SpecSerializer<SVal = Field::T>,
        Rest: SpecByteLen + SpecSerializer<SVal = Rest::T>,
     {
        type SVal = (Field::SVal, Rest::SVal);

        open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).spec_serialize(v)
        }
    }

    impl<Field, Rest, const DER: bool> SpecByteLen for DefaultedFmt<
        Field,
        Field::T,
        Rest,
        DER,
    > where Field: SpecByteLen, Rest: SpecByteLen {
        type T = (Field::T, Rest::T);

        open spec fn byte_len(&self, v: Self::T) -> nat {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<Field, Rest, const DER: bool> SafeParser for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + SafeParser<PVal = Field::T>,
        Rest: SpecByteLen + SafeParser<PVal = Rest::T>,
     {
        open spec fn safe_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_parse_safe(ibuf);
        }
    }

    impl<Field, Rest, const DER: bool> Productive for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + Productive<PVal = Field::T>,
        Rest: SpecByteLen + Productive<PVal = Rest::T>,
     {
        open spec fn productive_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).productive_inv()
        }

        proof fn lemma_productive(&self, s: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_productive(s);
        }
    }

    impl<Field, Rest, const DER: bool> SoundParser for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where Field: SoundParser, Rest: SoundParser {
        open spec fn sound_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).sound_inv()
        }

        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_parse_sound_consumption(
                ibuf,
            );
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_parse_sound_value(ibuf);
        }
    }

    impl<Field, Rest, const DER: bool> NonTailFmt for DefaultedFmt<
        Field,
        Field::SValue,
        Rest,
        DER,
    > where Field: NonTailFmt, Rest: NonTailFmt {
        open spec fn serialize_dps_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).serialize_dps_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_serialize_dps_prepend(
                v,
                obuf,
            );
        }

        proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_serialize_dps_len(
                v,
                obuf,
            );
        }
    }

    impl<Field, Rest, const DER: bool> GoodSerializer for DefaultedFmt<
        Field,
        Field::SVal,
        Rest,
        DER,
    > where Field: GoodSerializer, Rest: GoodSerializer {
        open spec fn serialize_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).serialize_inv()
        }

        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_serialize_len(v);
        }
    }

    impl<Field, Rest, const DER: bool> SPRoundTripDps for DefaultedFmt<
        Field,
        Field::T,
        Rest,
        DER,
    > where Field: SPRoundTripDps + NonTailFmt, Rest: SPRoundTripDps {
        open spec fn unambiguous(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).unambiguous()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(
                self.0,
                self.1,
                self.2,
            ).theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<Field, Rest, const DER: bool> NoLookAhead for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + NoLookAhead<PVal = Field::T>,
        Rest: SpecByteLen + NoLookAhead<PVal = Rest::T>,
     {
        open spec fn no_lookahead_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).no_lookahead_inv()
        }

        proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_no_lookahead(i1, i2);
        }
    }

    impl<Field, Rest, const DER: bool> NonMalleable for DefaultedFmt<
        Field,
        Field::PVal,
        Rest,
        DER,
    > where Field: SoundParser + NonMalleable, Rest: SoundParser + NonMalleable {
        open spec fn nonmal_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).nonmal_inv()
        }

        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_parse_non_malleable(
                buf1,
                buf2,
            );
        }
    }

    impl<Field, Rest, const DER: bool> EquivSerializersGeneral for DefaultedFmt<
        Field,
        Field::SVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + EquivSerializersGeneral<SVal = Field::T>,
        Rest: SpecByteLen + EquivSerializersGeneral<SVal = Rest::T>,
     {
        open spec fn equiv_general_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).equiv_general_inv()
        }

        proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).lemma_serialize_equiv(
                v,
                obuf,
            );
        }
    }

    impl<Field, Rest, const DER: bool> EquivSerializers for DefaultedFmt<
        Field,
        Field::SVal,
        Rest,
        DER,
    > where
        Field: SpecByteLen + EquivSerializersGeneral<SVal = Field::T>,
        Rest: SpecByteLen + EquivSerializers<SVal = Rest::T>,
     {
        open spec fn equiv_inv(&self) -> bool {
            defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2).equiv_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            defaulted_fmt::<Field, Rest, DER>(
                self.0,
                self.1,
                self.2,
            ).lemma_serialize_equiv_on_empty(v);
        }
    }

}

/*
 * TODO: Due to technical reasons, `DefaultedFmt` now only support `Structural` (in the Verus sense) types. To support non-Structural types,
 * `DefaultedFmt` needs to take both the `exec` default value and the `spec` default value, which is the `DeepView` of the `exec` default value.
 */

impl<I, Field, Rest, const DER: bool> Parser<I> for DefaultedFmt<Field, Field::T, Rest, DER> where
    I: InputBuf,
    Field: Parser<I, PT = Field::T> + SafeParser<PVal = Field::T> + SpecByteLen,
    Rest: Parser<I> + SafeParser<PVal = Rest::T> + SpecByteLen,
    Field::T: DeepView<V = Field::T> + PartialEq + Structural + Copy,
 {
    type PT = (Field::PT, Rest::PT);

    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.0.safe_inv()
        &&& self.2.exec_inv()
        &&& self.2.safe_inv()
        &&& forall|v: Field::T| v.deep_view() == v
        &&& vstd::laws_eq::obeys_concrete_eq::<Field::T>()
    }

    fn parse(&self, ibuf: &I) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        reveal(vstd::laws_eq::obeys_concrete_eq);

        let (n, (field, rest)) = Optional(&self.0, &self.2).parse(ibuf)?;

        if DER {
            if let Some(v) = field {
                if v == self.1 {
                    return Err(ParseError::non_canonical());
                }
            }
        }
        let field = match field {
            Some(v) => v,
            None => self.1,
        };

        Ok((n, (field, rest)))
    }
}

impl<Output: OutputBuf, Field, Default, Rest, R, const DER: bool> Serializer<
    Output,
    (Default, R),
> for DefaultedFmt<Field, Default, Rest, DER> where
    Field: SpecByteLen<T = Default> + Serializer<Output, Default>,
    Rest: SpecByteLen<T = R::V> + Serializer<Output, R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: Default| v.deep_view() == v
    }

    fn serialize_into(&self, v: &(Default, R), obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        if v.0 != self.1 {
            self.0.serialize_into(&v.0, obuf);
        }
        self.2.serialize_into(&v.1, obuf);
    }
}

impl<Field, Default, Rest, R, const DER: bool> Prepare<(Default, R)> for DefaultedFmt<
    Field,
    Default,
    Rest,
    DER,
> where
    Field: SpecByteLen<T = Default> + Prepare<Default>,
    Rest: SpecByteLen<T = R::V> + Prepare<R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: Default| v.deep_view() == v
    }

    fn prepare(&self, v: &(Default, R)) -> Result<usize, PreSerializeError> {
        let n0 = if v.0 == self.1 {
            0
        } else {
            self.0.prepare(&v.0)?
        };
        let n1 = self.2.prepare(&v.1)?;
        let total = n0.checked_add(n1).ok_or(PreSerializeError::length_too_large())?;
        Ok(total)
    }
}

impl<Field, Default, Rest, R, const DER: bool> ByteLen<(Default, R)> for DefaultedFmt<
    Field,
    Default,
    Rest,
    DER,
> where
    Field: SpecByteLen<T = Default> + ByteLen<Default>,
    Rest: SpecByteLen<T = R::V> + ByteLen<R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& self.0.exec_inv()
        &&& self.2.exec_inv()
        &&& forall|v: Default| v.deep_view() == v
    }

    fn length(&self, v: &(Default, R)) -> usize {
        let n0 = if v.0 == self.1 {
            0
        } else {
            self.0.length(&v.0)
        };
        let n1 = self.2.length(&v.1);
        n0 + n1
    }
}

} // verus!
