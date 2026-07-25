//! BER BIT STRING combinators with constructed/indefinite segment trees.
use crate::asn1::{
    constructed_tag, primitive_tag, ASN1Fmt, BerLength, BerLengthFmt, BitStringFmt, BitStringSpec,
    Class, LengthFmt, Tag, TagFmt, BER,
};
#[cfg(feature = "alloc")]
use crate::asn1::{BitString, BitStringOwned};
use crate::combinators::{
    bytes::ExactLen,
    mapped::spec::FnSpecMapper,
    recursive::{
        BundledSpecs, ParamRecSpecs, ParserRecBody, ProductiveRecBody, SafeParserRecBody,
        SpecRecBody,
    },
    tail::RepeatTillEnd,
    Bind, FixWith, Mapped, Refined, Repeat, Sum, Void,
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

type BerBitStringWireType = (
    Tag,
    Sum<
        (usize, BitStringSpec),
        Sum<(BerLength, Sum<Seq<BitStringSpec>, (Seq<BitStringSpec>, (u8, u8))>), Never>,
    >,
);

type BerBitStringRawBodyFmt<Rec> = Bind<
    TagFmt,
    spec_fn(Tag) -> Sum<
        Bind<LengthFmt<BER>, spec_fn(usize) -> ExactLen<BitStringFmt<BER>, usize>>,
        Sum<
            Bind<
                BerLengthFmt,
                spec_fn(BerLength) -> Sum<ExactLen<RepeatTillEnd<Rec>, usize>, Repeat<Rec, EocFmt>>,
            >,
            Void,
        >,
    >,
>;

type BerBitStringBodyFmt<Rec> = Mapped<
    Refined<BerBitStringRawBodyFmt<Rec>, PredFnSpec<BerBitStringWireType>>,
    FnSpecMapper<BerBitStringWireType, BitStringSpec>,
>;

/// Constructed BIT STRING segments are concatenable only when every segment except the last has
/// zero unused bits (X.690, 8.6.4.2).
pub open spec fn ber_bit_string_segments_wf(segments: Seq<BitStringSpec>) -> bool {
    forall|i: int| 0 <= i < segments.len() - 1 ==> #[trigger] segments[i].unused == 0
}

pub open spec fn flatten_ber_bit_string_segments(segments: Seq<BitStringSpec>) -> BitStringSpec {
    let bits = segments.map(|_i: int, segment: BitStringSpec| segment.bits).flatten();
    BitStringSpec {
        unused: if bits.len() == 0 || segments.len() == 0 {
            0
        } else {
            segments.last().unused
        },
        bits,
    }
}

pub open spec fn ber_bit_string_wire_wf(parsed: BerBitStringWireType) -> bool {
    match parsed.1 {
        L(_) => true,
        R(L((_length, inner))) => match inner {
            L(segments) => ber_bit_string_segments_wf(segments),
            R((segments, _eoc)) => ber_bit_string_segments_wf(segments),
        },
        R(R(_)) => true,
    }
}

/// One recursive unfolding of a BER BIT STRING.
///
/// IMPLICIT tagging replaces only the outer tag. Nested fragments retain universal BIT STRING
/// tag 3, as required by X.690, 8.6.4.1.
pub open spec fn ber_bit_string_rec_body(
    tag: Tag,
    rec: ParamRecSpecs<Tag, BitStringSpec>,
) -> BerBitStringBodyFmt<BundledSpecs<BitStringSpec>> {
    #[verusfmt::skip]
    Mapped {
        inner: Refined(
            Bind(TagFmt, |parsed_tag: Tag|
                match parsed_tag {
                    t if t == primitive_tag(tag) =>
                        L(Bind(LengthFmt::<BER>, |len: usize|
                            ExactLen(len, BitStringFmt::<BER>))),
                    t if t == constructed_tag(tag) =>
                        R(L(Bind(BerLengthFmt, |len: BerLength|
                            match len {
                                BerLength::Definite(len) =>
                                    L(ExactLen(len, RepeatTillEnd(rec(TagFmt::BIT_STRING)))),
                                BerLength::Indefinite =>
                                    R(Repeat(rec(TagFmt::BIT_STRING), EOC)),
                            }))),
                    _ => R(R(Void("Tag must match the configured BER BIT STRING identity"))),
                },
            ),
            |parsed: BerBitStringWireType| ber_bit_string_wire_wf(parsed),
        ),
        mapper: (
            |parsed: BerBitStringWireType|
                match parsed.1 {
                    L((_len, value)) => value,
                    R(L((_len, inner))) => match inner {
                        L(segments) => flatten_ber_bit_string_segments(segments),
                        R((segments, _eoc)) => flatten_ber_bit_string_segments(segments),
                    },
                    R(R(_)) => arbitrary(), // unreachable
                },
            |value: BitStringSpec| (
                primitive_tag(tag),
                L((BitStringFmt::<BER>.byte_len(value) as usize, value)),
            ),
        ),
    }
}

pub struct BerBitStringRecBody;

impl SpecRecBody for BerBitStringRecBody {
    type Param = Tag;

    type T = BitStringSpec;

    type Body = BerBitStringBodyFmt<BundledSpecs<BitStringSpec>>;

    open spec fn spec_body(
        &self,
        tag: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        ber_bit_string_rec_body(tag, rec)
    }
}

mod recursive_proofs {
    use super::*;

    impl SafeParserRecBody for BerBitStringRecBody {
        proof fn lemma_body_safe_inv_preservation(
            &self,
            _tag: Tag,
            _rec: ParamRecSpecs<Tag, BitStringSpec>,
        ) {
        }
    }

    impl ProductiveRecBody for BerBitStringRecBody {
        proof fn lemma_body_productive_inv_preservation(
            &self,
            _tag: Tag,
            _rec: ParamRecSpecs<Tag, BitStringSpec>,
        ) {
        }
    }

}

/// The primitive, definite-length BER encoding selected by the BIT STRING serializer.
pub open spec fn ber_bit_string_normalized_fmt(tag: Tag) -> ASN1Fmt<BitStringFmt<BER>, BER> {
    ASN1Fmt(primitive_tag(tag), BitStringFmt::<BER>)
}

/// BER BIT STRING with bounded constructed nesting and a configurable outer tag identity.
///
/// Parsing accepts primitive and constructed definite/indefinite forms. Serialization always
/// emits a primitive definite-length BER encoding.
#[derive(Clone, Copy)]
pub struct BerBitStringFmt<const LIMIT: usize>(pub Tag);

impl<const LIMIT: usize> BerBitStringFmt<LIMIT> {
    #[verifier::allow_in_spec]
    pub const fn universal() -> Self
        returns
            Self(TagFmt::BIT_STRING),
    {
        Self(TagFmt::BIT_STRING)
    }

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

    impl<const LIMIT: usize> SpecParser for BerBitStringFmt<LIMIT> {
        type PVal = BitStringSpec;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            FixWith::<LIMIT, _, _>(BerBitStringRecBody, self.0).spec_parse(ibuf)
        }
    }

    impl<const LIMIT: usize> Consistency for BerBitStringFmt<LIMIT> {
        type Val = BitStringSpec;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            ber_bit_string_normalized_fmt(self.0).consistent(value)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for BerBitStringFmt<LIMIT> {
        type SValue = BitStringSpec;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_bit_string_normalized_fmt(self.0).spec_serialize_dps(value, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for BerBitStringFmt<LIMIT> {
        type SVal = BitStringSpec;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_bit_string_normalized_fmt(self.0).spec_serialize(value)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for BerBitStringFmt<LIMIT> {
        type T = BitStringSpec;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_bit_string_normalized_fmt(self.0).byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const LIMIT: usize> SafeParser for BerBitStringFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerBitStringRecBody, self.0).lemma_parse_safe(ibuf);
        }
    }

    impl<const LIMIT: usize> Productive for BerBitStringFmt<LIMIT> {
        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            FixWith::<LIMIT, _, _>(BerBitStringRecBody, self.0).lemma_productive(ibuf);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for BerBitStringFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, value: BitStringSpec) {
            ber_bit_string_normalized_fmt(self.0).lemma_serialize_len(value);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for BerBitStringFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: BitStringSpec, obuf: Seq<u8>) {
            ber_bit_string_normalized_fmt(self.0).lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: BitStringSpec, obuf: Seq<u8>) {
            ber_bit_string_normalized_fmt(self.0).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for BerBitStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, value: BitStringSpec, obuf: Seq<u8>) {
            ber_bit_string_normalized_fmt(self.0).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for BerBitStringFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: BitStringSpec) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for BerBitStringFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: BitStringSpec, obuf: Seq<u8>) {
            ber_bit_string_normalized_fmt(self.0).theorem_serialize_dps_parse_roundtrip(
                value,
                obuf,
            );
        }
    }

}

impl<Output, T, const LIMIT: usize> Serializer<Output, T> for BerBitStringFmt<LIMIT> where
    Output: OutputBuf,
    T: DeepView<V = BitStringSpec> + ?Sized,
    ASN1Fmt<BitStringFmt<BER>, BER>: Serializer<Output, T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        <ASN1Fmt<BitStringFmt<BER>, BER> as Serializer<Output, T>>::exec_inv(
            &ber_bit_string_normalized_fmt(self.0),
        )
    }

    fn serialize_into(&self, value: &T, obuf: &mut Output) {
        let normalized = ASN1Fmt::<BitStringFmt<BER>, BER>(
            primitive_tag(self.0),
            BitStringFmt::<BER>,
        );
        normalized.serialize_into(value, obuf);
    }
}

impl<T, const LIMIT: usize> Prepare<T> for BerBitStringFmt<LIMIT> where
    T: DeepView<V = BitStringSpec> + ?Sized,
    ASN1Fmt<BitStringFmt<BER>, BER>: Prepare<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        <ASN1Fmt<BitStringFmt<BER>, BER> as Prepare<T>>::exec_inv(
            &ber_bit_string_normalized_fmt(self.0),
        )
    }

    fn prepare(&self, value: &T) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<BitStringFmt<BER>, BER>(
            primitive_tag(self.0),
            BitStringFmt::<BER>,
        );
        normalized.prepare(value)
    }
}

impl<T, const LIMIT: usize> ByteLen<T> for BerBitStringFmt<LIMIT> where
    T: DeepView<V = BitStringSpec> + ?Sized,
    ASN1Fmt<BitStringFmt<BER>, BER>: ByteLen<T>,
 {
    open spec fn exec_inv(&self) -> bool {
        <ASN1Fmt<BitStringFmt<BER>, BER> as ByteLen<T>>::exec_inv(
            &ber_bit_string_normalized_fmt(self.0),
        )
    }

    fn length(&self, value: &T) -> usize {
        let normalized = ASN1Fmt::<BitStringFmt<BER>, BER>(
            primitive_tag(self.0),
            BitStringFmt::<BER>,
        );
        normalized.length(value)
    }
}

#[cfg(feature = "alloc")]
fn bit_string_to_owned(value: BitString<'_, BER>) -> (owned: BitStringOwned)
    ensures
        owned.deep_view() == value.deep_view(),
{
    let unused = value.unused();
    let bits = slice_to_vec(value.bits());
    BitStringOwned::new(unused, bits)
}

#[cfg(feature = "alloc")]
fn ber_bit_string_segments_wf_exec(segments: &Vec<BitStringOwned>) -> (valid: bool)
    ensures
        valid == ber_bit_string_segments_wf(segments.deep_view()),
{
    let ghost views = segments.deep_view();
    let mut i = 0usize;
    while i < segments.len()
        invariant
            segments.deep_view() == views,
            i <= segments.len(),
            forall|j: int| 0 <= j < i && j < views.len() - 1 ==> #[trigger] views[j].unused == 0,
        decreases segments.len() - i,
    {
        if i + 1 < segments.len() {
            let unused = segments[i].unused();
            if unused != 0 {
                assert(0 <= i as int);
                assert((i as int) < views.len() - 1);
                assert(views[i as int].unused != 0);
                return false;
            }
        }
        i += 1;
    }
    true
}

#[cfg(feature = "alloc")]
fn flatten_bit_string_segments(segments: Vec<BitStringOwned>) -> (flat: BitStringOwned)
    requires
        ber_bit_string_segments_wf(segments.deep_view()),
    ensures
        flat.deep_view() == flatten_ber_bit_string_segments(segments.deep_view()),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    let ghost segment_views = segments.deep_view();
    let ghost bit_views = segment_views.map(|_i: int, segment: BitStringSpec| segment.bits);
    let mut bits = Vec::new();
    for i in 0..segments.len()
        invariant
            segments.deep_view() == segment_views,
            bit_views == segment_views.map(|_i: int, segment: BitStringSpec| segment.bits),
            bits@ == bit_views.take(i as int).flatten(),
    {
        let segment_bits = segments[i].bits();
        proof {
            let prefix = bit_views.take(i as int);
            prefix.lemma_flatten_push(segment_bits@);
            assert(bit_views[i as int] == segment_bits@);
            assert(bit_views.take(i as int + 1) == prefix.push(segment_bits@));
        }
        bits.extend_from_slice(segment_bits);
    }

    let unused = if bits.len() == 0 || segments.len() == 0 {
        0
    } else {
        let last = &segments[segments.len() - 1];
        last.unused()
    };
    BitStringOwned::new(unused, bits)
}

spec fn flattened_bit_string_result(result: Option<(int, Seq<BitStringSpec>)>) -> Option<
    (int, BitStringSpec),
> {
    match result {
        Some((n, segments)) if ber_bit_string_segments_wf(segments) => {
            Some((n, flatten_ber_bit_string_segments(segments)))
        },
        _ => None,
    }
}

spec fn flattened_bit_string_eoc_result(
    result: Option<(int, (Seq<BitStringSpec>, (u8, u8)))>,
) -> Option<(int, BitStringSpec)> {
    match result {
        Some((n, (segments, _eoc))) if ber_bit_string_segments_wf(segments) => {
            Some((n, flatten_ber_bit_string_segments(segments)))
        },
        _ => None,
    }
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_bit_string_segments<I, P>(parser: &P, ibuf: &I) -> (result: PResult<BitStringOwned>) where
    I: InputBuf,
    P: Parser<I, PT = Vec<BitStringOwned>, PVal = Seq<BitStringSpec>>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(result, flattened_bit_string_result(parser.spec_parse(ibuf@))),
{
    let (n, segments) = parser.parse(ibuf)?;
    if !ber_bit_string_segments_wf_exec(&segments) {
        return Err(
            ParseError::custom(
                "Only the final constructed BIT STRING segment may have unused bits",
            ),
        );
    }
    let flat = flatten_bit_string_segments(segments);
    Ok((n, flat))
}

#[inline(always)]
#[cfg(feature = "alloc")]
fn parse_bit_string_segments_eoc<I, P>(parser: &P, ibuf: &I) -> (result: PResult<
    BitStringOwned,
>) where
    I: InputBuf,
    P: Parser<I, PT = (Vec<BitStringOwned>, (u8, u8)), PVal = (Seq<BitStringSpec>, (u8, u8))>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(result, flattened_bit_string_eoc_result(parser.spec_parse(ibuf@))),
{
    let (n, (segments, _eoc)) = parser.parse(ibuf)?;
    if !ber_bit_string_segments_wf_exec(&segments) {
        return Err(
            ParseError::custom(
                "Only the final constructed BIT STRING segment may have unused bits",
            ),
        );
    }
    let flat = flatten_bit_string_segments(segments);
    Ok((n, flat))
}

#[cfg(feature = "alloc")]
impl<'i> ParserRecBody<&'i [u8]> for BerBitStringRecBody {
    type EP = Tag;

    type O = BitStringOwned;

    fn parse_body<Exec>(
        &self,
        expected: &Tag,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Tag, BitStringSpec>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<BitStringOwned> where Exec: Fn(&Tag, &&'i [u8]) -> PResult<BitStringOwned> {
        use crate::combinators::congruence::*;
        use crate::core::exec::bridge_lemmas::*;

        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use lemma_parser_congruent_reflexive;

        let _ = ibuf.len();
        let (tag_len, actual_tag) = TagFmt.parse(ibuf)?;
        let rest = ibuf.skip(tag_len);

        if actual_tag == primitive_tag(*expected) {
            let (length_len, content_len) = LengthFmt::<BER>.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let (content_len, value) = ExactLen(content_len, BitStringFmt::<BER>).parse(
                &content_bytes,
            )?;
            let value = bit_string_to_owned(value);
            Ok((tag_len + length_len + content_len, value))
        } else if actual_tag == constructed_tag(*expected) {
            let (length_len, content_len) = BerLengthFmt.parse(&rest)?;
            let content_bytes = rest.skip(length_len);
            let ghost child_spec = spec_rec(TagFmt::BIT_STRING);
            let child_exec = |input: &&'i [u8]| -> (r: PResult<BitStringOwned>)
                ensures
                    parse_matches_spec(r, child_spec.2(input@)),
                { exec_rec(&TagFmt::BIT_STRING, input) };
            let child: &FnParser<&'i [u8], BitStringOwned, BundledSpecs<BitStringSpec>, _> =
                &FnParser::new(child_exec, Ghost(child_spec));
            proof {
                lemma_ref_parser_exec_inv::<&'i [u8], _>(child);
                lemma_ref_safe_productive_inv(child);
                lemma_ref_fn_parser_congruence(child);
            }

            let (content_len, value) = match content_len {
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
                    parse_bit_string_segments(&exact, &content_bytes)?
                },
                BerLength::Indefinite => {
                    let repeated = Repeat(child, EOC);
                    proof {
                        lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                        lemma_repeat_parser_congruence(child, child_spec, EOC, EOC);
                        reveal(parser_congruent);
                    }
                    parse_bit_string_segments_eoc(&repeated, &content_bytes)?
                },
            };
            Ok((tag_len + length_len + content_len, value))
        } else {
            Err(ParseError::custom("Tag must match the configured BER BIT STRING identity"))
        }
    }
}

#[cfg(feature = "alloc")]
impl<'i, const LIMIT: usize> Parser<&'i [u8]> for BerBitStringFmt<LIMIT> {
    type PT = BitStringOwned;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        FixWith::<LIMIT, _, _>(BerBitStringRecBody, self.0).parse(ibuf)
    }
}

} // verus!
