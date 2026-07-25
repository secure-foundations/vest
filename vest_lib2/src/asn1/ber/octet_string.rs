//! BER OCTET STRING combinators with constructed/indefinite segment trees.
use crate::asn1::{
    constructed_tag, primitive_tag, ASN1Fmt, BerLength, BerLengthFmt, Class, LengthFmt,
    OctetStringFmt, Tag, TagFmt, BER,
};
use crate::combinators::{
    bytes::ExactLen,
    mapped::spec::FnSpecMapper,
    recursive::{
        BundledSpecs, ParamRecSpecs, ParserRecBody, ProductiveRecBody, SafeParserRecBody,
        SpecRecBody,
    },
    tail::RepeatTillEnd,
    Bind, FixWith, Mapped, Repeat, Sum, Void,
};
use crate::core::exec::fns::*;
use crate::core::exec::parser::*;
use crate::core::exec::{
    input::InputBuf, ByteLen, OutputBuf, PResult, ParseError, Parser, PreSerializeError, Prepare,
    Serializer,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::slice::slice_to_vec;

use super::any::{EocFmt, EOC};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

type BerOctetStringWireType = (
    Tag,
    Sum<(usize, Seq<u8>), Sum<(BerLength, Sum<Seq<Seq<u8>>, (Seq<Seq<u8>>, (u8, u8))>), Never>>,
);

type BerOctetStringBodyFmt<Rec> = Mapped<
    Bind<
        TagFmt,
        spec_fn(Tag) -> Sum<
            Bind<LengthFmt<BER>, spec_fn(usize) -> ExactLen<OctetStringFmt, usize>>,
            Sum<
                Bind<
                    BerLengthFmt,
                    spec_fn(BerLength) -> Sum<
                        ExactLen<RepeatTillEnd<Rec>, usize>,
                        Repeat<Rec, EocFmt>,
                    >,
                >,
                Void,
            >,
        >,
    >,
    FnSpecMapper<BerOctetStringWireType, Seq<u8>>,
>;

/// One full TLV unfolding of a BER OCTET STRING.
///
/// X.690, 8.23.3 specifies a restricted character string as
/// `[UNIVERSAL x] IMPLICIT OCTET STRING`. Thus `tag` applies only to the outermost TLV; constructed
/// fragments recursively use universal OCTET STRING tag 4, as required by X.690, 8.7.3.2.
pub open spec fn ber_octet_string_rec_body(
    tag: Tag,
    rec: ParamRecSpecs<Tag, Seq<u8>>,
) -> BerOctetStringBodyFmt<BundledSpecs<Seq<u8>>> {
    #[verusfmt::skip]
    Mapped {
        inner: Bind(TagFmt, |parsed_tag: Tag|
            match parsed_tag {
                t if t == primitive_tag(tag) =>
                    L(Bind(LengthFmt::<BER>, |len: usize| ExactLen(len, OctetStringFmt))),
                t if t == constructed_tag(tag) =>
                    R(L(Bind(BerLengthFmt, |len: BerLength|
                        match len {
                            BerLength::Definite(len) =>
                                L(ExactLen(len, RepeatTillEnd(rec(TagFmt::OCTET_STRING)))),
                            BerLength::Indefinite =>
                                R(Repeat(rec(TagFmt::OCTET_STRING), EOC)),
                        }))),
                _ => R(R(Void("Tag must match the configured BER OCTET STRING identity"))),
            },
        ),
        mapper: (
            |parsed: BerOctetStringWireType|
                match parsed.1 {
                    L((_len, bytes)) => bytes,
                    R(L((_len, inner))) => match inner {
                        L(segments) => segments.flatten(),
                        R((segments, _eoc)) => segments.flatten(),
                    },
                    R(R(_)) => arbitrary(), // unreachable
                },
            |bytes: Seq<u8>| (primitive_tag(tag), L((bytes.len() as usize, bytes))),
        ),
    }
}

pub struct BerOctetStringRecBody;

impl SpecRecBody for BerOctetStringRecBody {
    type Param = Tag;

    type T = Seq<u8>;

    type Body = BerOctetStringBodyFmt<BundledSpecs<Seq<u8>>>;

    open spec fn spec_body(
        &self,
        tag: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        ber_octet_string_rec_body(tag, rec)
    }
}

mod recursive_proofs {
    use super::*;

    impl SafeParserRecBody for BerOctetStringRecBody {
        proof fn lemma_body_safe_inv_preservation(
            &self,
            tag: Tag,
            rec: ParamRecSpecs<Tag, Seq<u8>>,
        ) {
        }
    }

    impl ProductiveRecBody for BerOctetStringRecBody {
        proof fn lemma_body_productive_inv_preservation(
            &self,
            tag: Tag,
            rec: ParamRecSpecs<Tag, Seq<u8>>,
        ) {
        }
    }

}

/// The primitive, definite-length encoding selected by the reverse mapper.
pub open spec fn ber_octet_string_normalized_fmt(tag: Tag) -> ASN1Fmt<OctetStringFmt, BER> {
    ASN1Fmt(primitive_tag(tag), OctetStringFmt)
}

/// BER OCTET STRING with bounded recursive nesting and a configurable outer tag identity.
///
/// Use [`Self::universal`] for an ordinary OCTET STRING or [`Self::implicit`] for an
/// IMPLICIT-tagged value. The stored tag's constructed bit is normalized away: parsing accepts
/// either primitive or constructed form and serialization always emits primitive definite form.
#[derive(Clone, Copy)]
pub struct BerOctetStringFmt<const LIMIT: usize>(pub Tag);

impl<const LIMIT: usize> BerOctetStringFmt<LIMIT> {
    /// Ordinary universal OCTET STRING.
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::OCTET_STRING),
    {
        Self(TagFmt::OCTET_STRING)
    }

    /// An IMPLICIT-tagged OCTET STRING. Only the outermost tag identity is replaced.
    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64) -> Self
        returns
            Self(
                Tag {
                    class,
                    constructed: false,
                    number: crate::asn1::tag::tag_num_from_uint(number),
                },
            ),
    {
        Self(Tag { class, constructed: false, number: crate::asn1::tag::tag_num_from_uint(number) })
    }
}

mod derived_specs {
    use super::*;

    impl<const LIMIT: usize> SpecParser for BerOctetStringFmt<LIMIT> {
        type PVal = Seq<u8>;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for BerOctetStringFmt<LIMIT> {
        type Val = Seq<u8>;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            ber_octet_string_normalized_fmt(self.0).consistent(value)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for BerOctetStringFmt<LIMIT> {
        type SValue = Seq<u8>;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_octet_string_normalized_fmt(self.0).spec_serialize_dps(value, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for BerOctetStringFmt<LIMIT> {
        type SVal = Seq<u8>;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_octet_string_normalized_fmt(self.0).spec_serialize(value)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for BerOctetStringFmt<LIMIT> {
        type T = Seq<u8>;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_octet_string_normalized_fmt(self.0).byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const LIMIT: usize> SafeParser for BerOctetStringFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> Productive for BerOctetStringFmt<LIMIT> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).lemma_productive(ibuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, value: Seq<u8>) {
            ber_octet_string_normalized_fmt(self.0).lemma_serialize_len(value);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.lemma_serialize_equiv(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for BerOctetStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Seq<u8>) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for BerOctetStringFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Seq<u8>, obuf: Seq<u8>) {
            let normalized = ber_octet_string_normalized_fmt(self.0);
            normalized.theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

impl<const LIMIT: usize, Output: OutputBuf> Serializer<Output, [u8]> for BerOctetStringFmt<LIMIT> {
    fn serialize_into(&self, value: &[u8], obuf: &mut Output) {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.serialize_into(value, obuf);
    }
}

impl<const LIMIT: usize> Prepare<[u8]> for BerOctetStringFmt<LIMIT> {
    fn prepare(&self, value: &[u8]) -> Result<usize, PreSerializeError> {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.prepare(value)
    }
}

impl<const LIMIT: usize> ByteLen<[u8]> for BerOctetStringFmt<LIMIT> {
    fn length(&self, value: &[u8]) -> usize {
        let tag = Tag { class: self.0.class, constructed: false, number: self.0.number };
        let normalized = ASN1Fmt::<OctetStringFmt, BER>(tag, OctetStringFmt);
        normalized.length(value)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize, Output: OutputBuf> Serializer<Output, Vec<u8>> for BerOctetStringFmt<
    LIMIT,
> {
    fn serialize_into(&self, value: &Vec<u8>, obuf: &mut Output) {
        self.serialize_into(value.as_slice(), obuf)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> Prepare<Vec<u8>> for BerOctetStringFmt<LIMIT> {
    fn prepare(&self, value: &Vec<u8>) -> Result<usize, PreSerializeError> {
        self.prepare(value.as_slice())
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> ByteLen<Vec<u8>> for BerOctetStringFmt<LIMIT> {
    fn length(&self, value: &Vec<u8>) -> usize {
        self.length(value.as_slice())
    }
}

#[cfg(feature = "alloc")]
fn flatten_octet_segments(segments: Vec<Vec<u8>>) -> (flat: Vec<u8>)
    ensures
        flat@ == segments.deep_view().flatten(),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    let mut flat = Vec::new();
    let ghost segment_views = segments.deep_view();
    for i in 0..segments.len()
        invariant
            segments.deep_view() == segment_views,
            flat@ == segment_views.take(i as int).flatten(),
    {
        let segment = &segments[i];
        proof {
            let prefix = segment_views.take(i as int);
            prefix.lemma_flatten_push(segment@);
            assert(segment_views[i as int] == segment@);
            assert(segment_views.take(i as int + 1) == prefix.push(segment@));
        }
        flat.extend_from_slice(&segment);
    }
    flat
}

spec fn flattened_result(r: Option<(int, Seq<Seq<u8>>)>) -> Option<(int, Seq<u8>)> {
    match r {
        Some((n, segments)) => Some((n, segments.flatten())),
        None => None,
    }
}

spec fn flattened_result_eoc(r: Option<(int, (Seq<Seq<u8>>, (u8, u8)))>) -> Option<(int, Seq<u8>)> {
    match r {
        Some((n, (segments, _eoc))) => Some((n, segments.flatten())),
        None => None,
    }
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_segments_flatten<I, P>(parser: &P, ibuf: &I) -> (r: PResult<Vec<u8>>) where
    I: InputBuf,
    P: Parser<I, PT = Vec<Vec<u8>>, PVal = Seq<Seq<u8>>>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(r, flattened_result(parser.spec_parse(ibuf@))),
{
    let (n, segments) = parser.parse(ibuf)?;
    let flat = flatten_octet_segments(segments);
    assert(flat.deep_view() == flat@);
    Ok((n, flat))
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_segments_eoc_flatten<I, P>(parser: &P, ibuf: &I) -> (r: PResult<Vec<u8>>) where
    I: InputBuf,
    P: Parser<I, PT = (Vec<Vec<u8>>, (u8, u8)), PVal = (Seq<Seq<u8>>, (u8, u8))>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(r, flattened_result_eoc(parser.spec_parse(ibuf@))),
{
    let (n, (segments, _eoc)) = parser.parse(ibuf)?;
    let flat = flatten_octet_segments(segments);
    assert(flat.deep_view() == flat@);
    Ok((n, flat))
}

#[cfg(feature = "alloc")]
impl<'i> ParserRecBody<&'i [u8]> for BerOctetStringRecBody {
    type EP = Tag;

    type O = Vec<u8>;

    fn parse_body<Exec>(
        &self,
        expected: &Tag,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Tag, Seq<u8>>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Vec<u8>> where Exec: Fn(&Tag, &&'i [u8]) -> PResult<Vec<u8>> {
        use crate::core::exec::bridge_lemmas::*;
        use crate::combinators::congruence::*;

        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use lemma_parser_congruent_reflexive;

        let _ = ibuf.len();
        let (tag_len, actual_tag) = TagFmt.parse(ibuf)?;
        let rest = ibuf.skip(tag_len);

        if actual_tag == primitive_tag(*expected) {
            let (length_len, content_len) = LengthFmt::<BER>.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let (content_len, v) = ExactLen(content_len, OctetStringFmt).parse(&content_bytes)?;
            let v = slice_to_vec(v);
            assert(v.deep_view() == v@);
            let total = tag_len + length_len + content_len;
            Ok((total, v))
        } else if actual_tag == constructed_tag(*expected) {
            let (length_len, content_len) = BerLengthFmt.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let ghost child_spec = spec_rec(TagFmt::OCTET_STRING);
            let child_exec = |input: &&'i [u8]| -> (r: PResult<Vec<u8>>)
                ensures
                    parse_matches_spec(r, child_spec.2(input@)),
                { exec_rec(&TagFmt::OCTET_STRING, input) };
            // The explicit spec type is required by ordinary rustc: the value of a
            // `Ghost<_>` is erased, so it cannot by itself drive type inference outside Verus.
            let child: &FnParser<&'i [u8], Vec<u8>, BundledSpecs<Seq<u8>>, _> = &FnParser::new(
                child_exec,
                Ghost(child_spec),
            );
            proof {
                lemma_ref_parser_exec_inv::<&'i [u8], _>(child);
                lemma_ref_safe_productive_inv(child);
                lemma_ref_fn_parser_congruence(child);
            }

            let (content_len, v) = match content_len {
                BerLength::Definite(content_len) => {
                    let ghost repeated_spec = RepeatTillEnd(child_spec);
                    let repeated = RepeatTillEnd(child);
                    let exact = ExactLen(content_len, repeated);
                    proof {
                        lemma_repeat_till_end_parser_exec_inv::<&'i [u8], _>(&repeated);
                        lemma_exact_len_parser_exec_inv::<&'i [u8], _, _>(&exact);
                        lemma_repeat_till_end_parser_congruence(child, child_spec);
                        lemma_exact_len_parser_congruence(content_len, repeated, repeated_spec);
                        reveal(parser_congruent);
                    }
                    parse_segments_flatten(&exact, &content_bytes)?
                },
                BerLength::Indefinite => {
                    let repeated = Repeat(child, EOC);
                    proof {
                        lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                        lemma_repeat_parser_congruence(child, child_spec, EOC, EOC);
                        reveal(parser_congruent);
                    }
                    parse_segments_eoc_flatten(&repeated, &content_bytes)?
                },
            };
            let total = tag_len + length_len + content_len;
            Ok((total, v))
        } else {
            Err(ParseError::custom("Tag must match the configured BER OCTET STRING identity"))
        }
    }
}

#[cfg(feature = "alloc")]
impl<'i, const LIMIT: usize> Parser<&'i [u8]> for BerOctetStringFmt<LIMIT> {
    type PT = Vec<u8>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        FixWith::<LIMIT, _, _>(BerOctetStringRecBody, self.0).parse(ibuf)
    }
}

} // verus!
