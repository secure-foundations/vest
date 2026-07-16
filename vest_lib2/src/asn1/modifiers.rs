//! ASN.1 component modifiers.
//!
//! IMPLICIT and EXPLICIT tagging reduce directly to [`ASN1Fmt`]. OPTIONAL uses
//! [`Optional`](crate::combinators::Optional). DEFAULT is a derived
//! `Mapped<Refined<Optional<...>, ...>, ...>` format: BER accepts an explicitly
//! encoded default while DER rejects it, and both serializers omit defaults.
use crate::asn1::tag::{Class, TagNumber};
use crate::asn1::{ASN1Fmt, Tag};
use crate::combinators::mapped::spec::{FnSpecMapper, SpecMapper};
use crate::combinators::{Mapped, Optional, Refined};
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

/// Apply an ASN.1 IMPLICIT tag. The base type's primitive/constructed form is preserved.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn Implicit<C, const DER: bool>(class: Class, number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<
    C,
    DER,
>
    returns
        ASN1Fmt::<_, DER>(
            Tag {
                class,
                constructed: inner.0.constructed,
                number: super::tag::uint_to_tag_num(number),
            },
            inner.1,
        ),
{
    ASN1Fmt(Tag { class, constructed: inner.0.constructed, number: number.into() }, inner.1)
}

/// Apply an ASN.1 EXPLICIT tag. The outer tag is always constructed.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn Explicit<C, const DER: bool>(class: Class, number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<
    ASN1Fmt<C, DER>,
    DER,
>
    returns
        ASN1Fmt::<ASN1Fmt<_, DER>, DER>(
            Tag { class, constructed: true, number: super::tag::uint_to_tag_num(number) },
            inner,
        ),
{
    ASN1Fmt(Tag { class, constructed: true, number: number.into() }, inner)
}

/// Apply an ASN.1 context-specific IMPLICIT tag.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn ContextImplicit<C, const DER: bool>(number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<C, DER>
    returns
        Implicit(Class::ContextSpecific, number, inner),
{
    Implicit(Class::ContextSpecific, number, inner)
}

/// Apply an ASN.1 context-specific EXPLICIT tag.
#[allow(non_snake_case)]
#[verifier::allow_in_spec]
pub fn ContextExplicit<C, const DER: bool>(number: u64, inner: ASN1Fmt<C, DER>) -> ASN1Fmt<
    ASN1Fmt<C, DER>,
    DER,
>
    returns
        Explicit(Class::ContextSpecific, number, inner),
{
    Explicit(Class::ContextSpecific, number, inner)
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
    Rest: SpecByteLen<T = R> + Serializer<Output, R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView<V = R>,
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
    Rest: SpecByteLen<T = R> + Prepare<R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView<V = R>,
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
    Rest: SpecByteLen<T = R> + ByteLen<R>,
    Default: DeepView<V = Default> + PartialEq + Structural + Copy,
    R: DeepView<V = R>,
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

/// ASN.1 TLVs with distinct tags have disjoint parse domains.
pub broadcast proof fn lemma_disjoint_asn1_tags<
    A: SpecCombinator,
    B: SpecCombinator,
    const DER: bool,
>(a: ASN1Fmt<A, DER>, b: ASN1Fmt<B, DER>)
    requires
        a.0 != b.0,
    ensures
        #[trigger] disjoint_domains(a, b),
{
    reveal(disjoint_domains);
}

/// A [`DefaultedFmt<A, B>`] parser is disjoint from another parser if both `A` and `B` are.
pub broadcast proof fn lemma_disjoint_defaulted<P, A, B>(
    p: P,
    defaulted: DefaultedFmt<A, A::PVal, B, true>,
) where
    P: SpecParser,
    A: SpecByteLen + SpecParser<PVal = A::T>,
    B: SpecByteLen + SpecParser<PVal = B::T>,

    requires
        disjoint_domains(p, defaulted.0),
        disjoint_domains(p, defaulted.2),
    ensures
        #[trigger] disjoint_domains(p, defaulted),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

} // verus!
