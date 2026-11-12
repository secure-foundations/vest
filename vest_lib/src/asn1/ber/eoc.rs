//! BER end-of-contents marker and consuming unit-valued terminal.
//!
//! `EOC` recognizes the exact marker `00 00` and returns its tag/length pair.
//! `EOC_END` recognizes the same bytes but returns `()`, so
//! [`BerSeqBody`](super::sequence::BerSeqBody) can replace an EOF terminal
//! without changing the schema's value type.
use crate::asn1::{Tag, TagFmt};
use crate::combinators::{Const, Eof, Pair, U8};
use crate::core::exec::parser::*;
use crate::core::exec::{ByteLen, InputBuf, OutputBuf, PreSerializeError, Prepare, Serializer};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Exact BER end-of-contents marker: the universal primitive EOC tag followed by a zero length
/// octet (`00 00`).
pub type EocFmt = Pair<Const<TagFmt, Tag>, Const<U8, u8>>;

/// Parsed value of [`EocFmt`]. BER framing discards this value after recognizing the marker.
pub(super) type EocValue = (Tag, u8);

/// Exact BER end-of-contents marker (`00 00`).
pub const EOC: EocFmt = Pair(Const(TagFmt, TagFmt::EOC), Const(U8, 0u8));

/// Drop the marker value returned by a terminated parser, retaining its consumed length.
pub(super) open spec fn discard_eoc_result<T>(result: Option<(int, (T, EocValue))>) -> Option<
    (int, T),
> {
    match result {
        Some((n, (value, _eoc))) => Some((n, value)),
        None => None,
    }
}

/// Execute a terminated parser and discard only its EOC value.
pub(super) fn parse_discard_eoc<I, P, T>(parser: &P, input: &I) -> (result: PResult<T>) where
    I: InputBuf,
    T: DeepView,
    P: Parser<I, PT = (T, EocValue), PVal = (T::V, EocValue)>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(result, discard_eoc_result(parser.spec_parse(input@))),
{
    let (n, (value, _eoc)) = parser.parse(input)?;
    Ok((n, value))
}

/// Consumes and serializes EOC, returning `()` like [`Eof`].
#[derive(Clone, Copy)]
pub struct EocEndFmt;

/// Consuming terminal for an indefinite-length schema body.
pub const EOC_END: EocEndFmt = EocEndFmt;

proof fn lemma_eoc()
    ensures
        EOC.consistent((TagFmt::EOC, 0u8)),
        EOC.byte_len((TagFmt::EOC, 0u8)) == 2,
{
    crate::asn1::tag::lemma_tag_wf_implies_tag_consistent(TagFmt::EOC);
}

impl SpecParser for EocEndFmt {
    type PVal = ();

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, ())> {
        match EOC.spec_parse(input) {
            Some((n, _)) => Some((n, ())),
            None => None,
        }
    }
}

impl Consistency for EocEndFmt {
    type Val = ();

    open spec fn consistent(&self, _value: ()) -> bool {
        true
    }
}

impl SpecSerializer for EocEndFmt {
    type SVal = ();

    open spec fn spec_serialize(&self, _value: ()) -> Seq<u8> {
        EOC.spec_serialize((TagFmt::EOC, 0u8))
    }
}

impl SpecSerializerDps for EocEndFmt {
    type SValue = ();

    open spec fn spec_serialize_dps(&self, _value: (), suffix: Seq<u8>) -> Seq<u8> {
        EOC.spec_serialize_dps((TagFmt::EOC, 0u8), suffix)
    }
}

impl SpecByteLen for EocEndFmt {
    type T = ();

    open spec fn byte_len(&self, _value: ()) -> nat {
        2
    }
}

impl SafeParser for EocEndFmt {
    proof fn lemma_parse_safe(&self, input: Seq<u8>) {
        EOC.lemma_parse_safe(input);
    }
}

impl SoundParser for EocEndFmt {
    proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
    }
}

impl StrictParser for EocEndFmt {
    proof fn lemma_parse_strict_consumption(&self, input: Seq<u8>) {
        lemma_eoc();
        EOC.lemma_parse_sound_value(input);
        EOC.lemma_parse_strict_consumption(input);
    }
}

impl AdmitsUniqueVal for EocEndFmt {
    proof fn lemma_unique_consistent_val(&self, _left: (), _right: ()) {
    }
}

impl Productive for EocEndFmt {
    proof fn lemma_productive(&self, input: Seq<u8>) {
        EOC.lemma_productive(input);
    }
}

impl GoodSerializer for EocEndFmt {
    proof fn lemma_serialize_len(&self, _value: ()) {
        lemma_eoc();
        EOC.lemma_serialize_len((TagFmt::EOC, 0u8));
    }
}

impl NonTailFmt for EocEndFmt {
    proof fn lemma_serialize_dps_prepend(&self, _value: (), suffix: Seq<u8>) {
        EOC.lemma_serialize_dps_prepend((TagFmt::EOC, 0u8), suffix);
    }

    proof fn lemma_serialize_dps_len(&self, _value: (), suffix: Seq<u8>) {
        lemma_eoc();
        EOC.lemma_serialize_dps_len((TagFmt::EOC, 0u8), suffix);
    }
}

impl EquivSerializersGeneral for EocEndFmt {
    proof fn lemma_serialize_equiv(&self, _value: (), suffix: Seq<u8>) {
        EOC.lemma_serialize_equiv((TagFmt::EOC, 0u8), suffix);
    }
}

impl EquivSerializers for EocEndFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, value: ()) {
        self.lemma_serialize_equiv(value, Seq::empty());
    }
}

impl SPRoundTripDps for EocEndFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, _value: (), suffix: Seq<u8>) {
        lemma_eoc();
        EOC.theorem_serialize_dps_parse_roundtrip((TagFmt::EOC, 0u8), suffix);
    }
}

impl NonMalleable for EocEndFmt {
    proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
        lemma_eoc();
        EOC.lemma_parse_sound_value(left);
        EOC.lemma_parse_sound_value(right);
        EOC.lemma_parse_non_malleable(left, right);
    }
}

impl NoLookAhead for EocEndFmt {
    proof fn lemma_no_lookahead(&self, left: Seq<u8>, right: Seq<u8>) {
        EOC.lemma_no_lookahead(left, right);
    }
}

impl<'i> Parser<&'i [u8]> for EocEndFmt {
    type PT = ();

    fn min_byte_len(&self) -> usize {
        2
    }

    fn parse(&self, input: &&'i [u8]) -> PResult<()> {
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;

        proof {
            crate::core::exec::bridge_lemmas::lemma_pair_parser_exec_inv::<&'i [u8], _, _>(&EOC);
        }
        let (n, _) = EOC.parse(input)?;
        Ok((n, ()))
    }
}

impl<Output: OutputBuf> Serializer<Output, ()> for EocEndFmt {
    fn serialize_into(&self, _value: &(), output: &mut Output) {
        proof {
            lemma_eoc();
        }
        EOC.serialize_into(&(TagFmt::EOC, 0u8), output);
    }
}

impl Prepare<()> for EocEndFmt {
    fn prepare(&self, _value: &()) -> Result<usize, PreSerializeError> {
        Ok(2)
    }
}

impl ByteLen<()> for EocEndFmt {
    fn length(&self, _value: &()) -> usize {
        2
    }
}

} // verus!
#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::exec::SerializerExt;

    #[test]
    fn eoc_is_exactly_the_canonical_tag_and_zero_length_octet() {
        let input = [0x00, 0x00, 0xff];
        assert_eq!(EOC.parse(&&input[..]).unwrap(), (2, (TagFmt::EOC, 0u8)),);

        for invalid in [
            &[0x00][..],
            &[0x00, 0x01],
            &[0x20, 0x00],
            &[0x40, 0x00],
            &[0x1f, 0x00, 0x00],
        ] {
            assert!(EOC.parse(&invalid).is_err());
            assert!(EOC_END.parse(&invalid).is_err());
        }

        let value = (TagFmt::EOC, 0u8);
        let mut output = [0xff; 2];
        assert_eq!(EOC.prepare(&value).unwrap(), output.len());
        EOC.serialize(&value, output.as_mut_slice());
        assert_eq!(output, [0x00, 0x00]);
    }

    #[test]
    fn unit_terminal_consumes_and_serializes_the_marker() {
        let input = [0x00, 0x00, 0xaa];
        assert_eq!(EOC_END.parse(&&input[..]).unwrap(), (2, ()));
        assert_eq!(EOC_END.prepare(&()).unwrap(), 2);
        assert_eq!(EOC_END.length(&()), 2);
        let mut output = [0xff; 2];
        EOC_END.serialize(&(), &mut output);
        assert_eq!(output, [0x00, 0x00]);
    }
}
