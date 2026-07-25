//! Disjointness proofs for ASN.1 formats.
use super::ber::*;
use super::ber::{
    BerBitStringFmt, BerCharStringFmt, BerOctetStringFmt, BerOctetStringRecBody, BerSequenceFmt,
    BerSequenceOfFmt,
};
use super::modifiers::{DefaultedFmt, ImplicitlyTaggedFmt, Retaggable};
use super::{ASN1Fmt, Tag, TagFmt};
use crate::combinators::recursive::{FixWith, ParamRecSpecs};
use crate::combinators::Const;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// Ordinary ASN.1 TLVs with distinct complete wire tags have disjoint parse domains.
pub broadcast proof fn lemma_disjoint_asn1_tags<
    A: SpecCombinator,
    B: SpecCombinator,
    const DER: bool,
>(left: ASN1Fmt<A, DER>, right: ASN1Fmt<B, DER>)
    requires
        left.0 != right.0,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// BER SEQUENCE formats with distinct complete outer tags have disjoint parse domains.
pub broadcast proof fn lemma_disjoint_ber_sequences<A: SpecCombinator, B: SpecCombinator>(
    left: BerSequenceFmt<A>,
    right: BerSequenceFmt<B>,
)
    requires
        left.0 != right.0,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// BER SEQUENCE OF formats with distinct complete outer tags have disjoint parse domains.
pub broadcast proof fn lemma_disjoint_ber_sequence_ofs<A: SpecCombinator, B: SpecCombinator>(
    left: BerSequenceOfFmt<A>,
    right: BerSequenceOfFmt<B>,
)
    requires
        left.0 != right.0,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE and BER SEQUENCE OF with distinct complete outer tags are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_sequence_of<
    A: SpecCombinator,
    B: SpecCombinator,
>(sequence: BerSequenceFmt<A>, sequence_of: BerSequenceOfFmt<B>)
    requires
        sequence.0 != sequence_of.0,
    ensures
        #[trigger] disjoint_domains(sequence, sequence_of),
        #[trigger] disjoint_domains(sequence_of, sequence),
{
    reveal(disjoint_domains);
}

/// An ordinary ASN.1 TLV and BER SEQUENCE with distinct complete outer tags are disjoint.
pub broadcast proof fn lemma_disjoint_asn1_ber_sequence<
    A: SpecCombinator,
    B: SpecCombinator,
    const DER: bool,
>(asn1: ASN1Fmt<A, DER>, sequence: BerSequenceFmt<B>)
    requires
        asn1.0 != sequence.0,
    ensures
        #[trigger] disjoint_domains(asn1, sequence),
        #[trigger] disjoint_domains(sequence, asn1),
{
    reveal(disjoint_domains);
}

/// An ordinary ASN.1 TLV and BER SEQUENCE OF with distinct complete outer tags are disjoint.
pub broadcast proof fn lemma_disjoint_asn1_ber_sequence_of<
    A: SpecCombinator,
    B: SpecCombinator,
    const DER: bool,
>(asn1: ASN1Fmt<A, DER>, sequence_of: BerSequenceOfFmt<B>)
    requires
        asn1.0 != sequence_of.0,
    ensures
        #[trigger] disjoint_domains(asn1, sequence_of),
        #[trigger] disjoint_domains(sequence_of, asn1),
{
    reveal(disjoint_domains);
}

/// BER OCTET STRING formats with different tag class or number are disjoint.
pub broadcast proof fn lemma_disjoint_ber_octet_strings<const LEFT: usize, const RIGHT: usize>(
    left: BerOctetStringFmt<LEFT>,
    right: BerOctetStringFmt<RIGHT>,
)
    requires
        left.0.class != right.0.class || left.0.number != right.0.number,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// An ordinary ASN.1 TLV and BER OCTET STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_asn1_ber_octet_string<
    A: SpecCombinator,
    const DER: bool,
    const LIMIT: usize,
>(asn1: ASN1Fmt<A, DER>, octets: BerOctetStringFmt<LIMIT>)
    requires
        asn1.0.class != octets.0.class || asn1.0.number != octets.0.number,
    ensures
        #[trigger] disjoint_domains(asn1, octets),
        #[trigger] disjoint_domains(octets, asn1),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE and BER OCTET STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_octet_string<
    A: SpecCombinator,
    const LIMIT: usize,
>(sequence: BerSequenceFmt<A>, octets: BerOctetStringFmt<LIMIT>)
    requires
        sequence.0.class != octets.0.class || sequence.0.number != octets.0.number,
    ensures
        #[trigger] disjoint_domains(sequence, octets),
        #[trigger] disjoint_domains(octets, sequence),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE OF and BER OCTET STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_of_octet_string<
    A: SpecCombinator,
    const LIMIT: usize,
>(sequence_of: BerSequenceOfFmt<A>, octets: BerOctetStringFmt<LIMIT>)
    requires
        sequence_of.0.class != octets.0.class || sequence_of.0.number != octets.0.number,
    ensures
        #[trigger] disjoint_domains(sequence_of, octets),
        #[trigger] disjoint_domains(octets, sequence_of),
{
    reveal(disjoint_domains);
}

/// BER restricted character strings with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_char_strings<
    A: SpecCombinator,
    B: SpecCombinator,
    const LEFT: usize,
    const RIGHT: usize,
>(left: BerCharStringFmt<A, LEFT>, right: BerCharStringFmt<B, RIGHT>)
    requires
        left.0.class != right.0.class || left.0.number != right.0.number,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// An ordinary ASN.1 TLV and BER restricted character string with different identities are
/// disjoint.
pub broadcast proof fn lemma_disjoint_asn1_ber_char_string<
    A: SpecCombinator,
    C: SpecCombinator,
    const DER: bool,
    const LIMIT: usize,
>(asn1: ASN1Fmt<A, DER>, string: BerCharStringFmt<C, LIMIT>)
    requires
        asn1.0.class != string.0.class || asn1.0.number != string.0.number,
    ensures
        #[trigger] disjoint_domains(asn1, string),
        #[trigger] disjoint_domains(string, asn1),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE and restricted character string with different identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_char_string<
    A: SpecCombinator,
    C: SpecCombinator,
    const LIMIT: usize,
>(sequence: BerSequenceFmt<A>, string: BerCharStringFmt<C, LIMIT>)
    requires
        sequence.0.class != string.0.class || sequence.0.number != string.0.number,
    ensures
        #[trigger] disjoint_domains(sequence, string),
        #[trigger] disjoint_domains(string, sequence),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE OF and restricted character string with different identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_of_char_string<
    A: SpecCombinator,
    C: SpecCombinator,
    const LIMIT: usize,
>(sequence_of: BerSequenceOfFmt<A>, string: BerCharStringFmt<C, LIMIT>)
    requires
        sequence_of.0.class != string.0.class || sequence_of.0.number != string.0.number,
    ensures
        #[trigger] disjoint_domains(sequence_of, string),
        #[trigger] disjoint_domains(string, sequence_of),
{
    reveal(disjoint_domains);
}

/// BER OCTET STRING and restricted character string formats with different identities are
/// disjoint.
pub broadcast proof fn lemma_disjoint_ber_octet_char_string<
    C: SpecCombinator,
    const OCTETS: usize,
    const STRING: usize,
>(octets: BerOctetStringFmt<OCTETS>, string: BerCharStringFmt<C, STRING>)
    requires
        octets.0.class != string.0.class || octets.0.number != string.0.number,
    ensures
        #[trigger] disjoint_domains(octets, string),
        #[trigger] disjoint_domains(string, octets),
{
    reveal(disjoint_domains);
}

/// BER BIT STRING formats with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_bit_strings<const LEFT: usize, const RIGHT: usize>(
    left: BerBitStringFmt<LEFT>,
    right: BerBitStringFmt<RIGHT>,
)
    requires
        left.0.class != right.0.class || left.0.number != right.0.number,
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

/// An ordinary ASN.1 TLV and BER BIT STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_asn1_ber_bit_string<
    A: SpecCombinator,
    const DER: bool,
    const LIMIT: usize,
>(asn1: ASN1Fmt<A, DER>, bits: BerBitStringFmt<LIMIT>)
    requires
        asn1.0.class != bits.0.class || asn1.0.number != bits.0.number,
    ensures
        #[trigger] disjoint_domains(asn1, bits),
        #[trigger] disjoint_domains(bits, asn1),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE and BER BIT STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_bit_string<
    A: SpecCombinator,
    const LIMIT: usize,
>(sequence: BerSequenceFmt<A>, bits: BerBitStringFmt<LIMIT>)
    requires
        sequence.0.class != bits.0.class || sequence.0.number != bits.0.number,
    ensures
        #[trigger] disjoint_domains(sequence, bits),
        #[trigger] disjoint_domains(bits, sequence),
{
    reveal(disjoint_domains);
}

/// A BER SEQUENCE OF and BER BIT STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_sequence_of_bit_string<
    A: SpecCombinator,
    const LIMIT: usize,
>(sequence: BerSequenceOfFmt<A>, bits: BerBitStringFmt<LIMIT>)
    requires
        sequence.0.class != bits.0.class || sequence.0.number != bits.0.number,
    ensures
        #[trigger] disjoint_domains(sequence, bits),
        #[trigger] disjoint_domains(bits, sequence),
{
    reveal(disjoint_domains);
}

/// BER OCTET STRING and BER BIT STRING with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_octet_bit_string<const OCTETS: usize, const BITS: usize>(
    octets: BerOctetStringFmt<OCTETS>,
    bits: BerBitStringFmt<BITS>,
)
    requires
        octets.0.class != bits.0.class || octets.0.number != bits.0.number,
    ensures
        #[trigger] disjoint_domains(octets, bits),
        #[trigger] disjoint_domains(bits, octets),
{
    reveal(disjoint_domains);
}

/// BER BIT STRING and restricted character strings with different tag identities are disjoint.
pub broadcast proof fn lemma_disjoint_ber_bit_char_string<
    C: SpecCombinator,
    const BITS: usize,
    const STRING: usize,
>(bits: BerBitStringFmt<BITS>, string: BerCharStringFmt<C, STRING>)
    requires
        bits.0.class != string.0.class || bits.0.number != string.0.number,
    ensures
        #[trigger] disjoint_domains(bits, string),
        #[trigger] disjoint_domains(string, bits),
{
    reveal(disjoint_domains);
}

/// IMPLICIT tagging delegates its parse domain to the concretely retagged format.
pub broadcast proof fn lemma_disjoint_implicitly_tagged_left<F, P>(
    implicit: ImplicitlyTaggedFmt<F>,
    other: P,
) where F: Retaggable, F::Retagged: SpecParser, P: SpecParser
    requires
        disjoint_domains(implicit.1.spec_retagged(implicit.0), other),
    ensures
        #[trigger] disjoint_domains(implicit, other),
{
    reveal(disjoint_domains);
}

/// IMPLICIT tagging delegates its parse domain to the concretely retagged format.
pub broadcast proof fn lemma_disjoint_implicitly_tagged_right<P, F>(
    other: P,
    implicit: ImplicitlyTaggedFmt<F>,
) where P: SpecParser, F: Retaggable, F::Retagged: SpecParser
    requires
        disjoint_domains(other, implicit.1.spec_retagged(implicit.0)),
    ensures
        #[trigger] disjoint_domains(other, implicit),
{
    reveal(disjoint_domains);
}

/// A defaulted parser is disjoint from another parser if both of its branches are.
pub broadcast proof fn lemma_disjoint_defaulted<P, A, B, const DER: bool>(
    parser: P,
    defaulted: DefaultedFmt<A, A::PVal, B, DER>,
) where
    P: SpecParser,
    A: SpecByteLen + SpecParser<PVal = A::T>,
    B: SpecByteLen + SpecParser<PVal = B::T>,

    requires
        disjoint_domains(parser, defaulted.0),
        disjoint_domains(parser, defaulted.2),
    ensures
        #[trigger] disjoint_domains(parser, defaulted),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// Leaf and modifier disjointness lemmas for ASN.1 formats.
pub broadcast group asn1_disjointness_lemmas {
    lemma_disjoint_asn1_tags,
    lemma_disjoint_ber_sequences,
    lemma_disjoint_ber_sequence_ofs,
    lemma_disjoint_ber_sequence_sequence_of,
    lemma_disjoint_asn1_ber_sequence,
    lemma_disjoint_asn1_ber_sequence_of,
    lemma_disjoint_ber_octet_strings,
    lemma_disjoint_asn1_ber_octet_string,
    lemma_disjoint_ber_sequence_octet_string,
    lemma_disjoint_ber_sequence_of_octet_string,
    lemma_disjoint_ber_char_strings,
    lemma_disjoint_asn1_ber_char_string,
    lemma_disjoint_ber_sequence_char_string,
    lemma_disjoint_ber_sequence_of_char_string,
    lemma_disjoint_ber_octet_char_string,
    lemma_disjoint_ber_bit_strings,
    lemma_disjoint_asn1_ber_bit_string,
    lemma_disjoint_ber_sequence_bit_string,
    lemma_disjoint_ber_sequence_of_bit_string,
    lemma_disjoint_ber_octet_bit_string,
    lemma_disjoint_ber_bit_char_string,
    lemma_disjoint_implicitly_tagged_left,
    lemma_disjoint_implicitly_tagged_right,
    lemma_disjoint_defaulted,
}

} // verus!
