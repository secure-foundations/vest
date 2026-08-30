//! Compositional disjointness proofs for complete ASN.1 formats.
//!
//! Each complete ASN.1 format exposes an over-approximation of
//! what can occur at the start of an accepted input, and one
//! generic theorem turns disjoint start domains into `disjoint_domains`.
//! Adding another ASN.1 format therefore needs one start-domain proof
//! rather than pairwise proofs against every existing format.
use super::ber::*;
use super::modifiers::{DefaultedFmt, ImplicitlyTaggedFmt, Retaggable};
#[cfg(verus_only)]
use super::tag::tag_num_to_uint;
use super::tag::{tag_num_from_uint, TagNumber};
use super::{ASN1Fmt, AnyFmt, Class, Tag, TagFmt};
use crate::combinators::mapped::spec::{BiMap, SpecMap, SpecMapper};
use crate::combinators::{Alt, Choice, Const, Eof, Mapped, Named, Optional, Pair, Ref, Refined};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// The 256 possible ASN.1 identifier leading octets, split into one 64-bit word per class.
///
/// Within each word, bits `0..31` represent primitive identifiers and bits `32..63` represent
/// constructed identifiers. For tag numbers `0..30`, the low five bits identify the exact tag.
/// Bit 31 in either half is deliberately conservative: it represents every high-tag-number form
/// (`number >= 31`) having that class and constructed bit. Consequently this common-path
/// certificate cannot prove two different high tag numbers disjoint when they otherwise share
/// their first identifier octet.
#[verifier::ext_equal]
pub ghost struct Asn1TagLeadMask {
    pub universal: u64,
    pub application: u64,
    pub context_specific: u64,
    pub private: u64,
}

/// A conservative FIRST certificate for an ASN.1 parser.
///
/// `accepts_empty` covers EOF-like formats. Non-empty accepted inputs must begin with an ASN.1
/// identifier represented by `tags`.
#[verifier::ext_equal]
pub ghost struct Asn1StartDomain {
    pub accepts_empty: bool,
    pub tags: Asn1TagLeadMask,
}

#[verifier::inline]
pub open spec fn empty_tag_lead_mask() -> Asn1TagLeadMask {
    Asn1TagLeadMask { universal: 0, application: 0, context_specific: 0, private: 0 }
}

/// Construct a canonical, fixed-size ASN.1 FIRST certificate from its four bitmap words.
#[verifier::inline]
pub open spec fn asn1_start_mask(
    accepts_empty: bool,
    universal: u64,
    application: u64,
    context_specific: u64,
    private: u64,
) -> Asn1StartDomain {
    Asn1StartDomain {
        accepts_empty,
        tags: Asn1TagLeadMask { universal, application, context_specific, private },
    }
}

#[verifier::inline]
pub open spec fn tag_lead_low(number: TagNumber) -> u64 {
    let value = tag_num_to_uint(number);
    if value < 31u64 {
        value
    } else {
        31u64
    }
}

#[verifier::inline]
pub open spec fn tag_lead_index(tag: Tag) -> u64 {
    let low = tag_lead_low(tag.number);
    if tag.constructed {
        low | 32u64
    } else {
        low
    }
}

#[verifier::inline]
pub open spec fn tag_lead_bit(tag: Tag) -> u64 {
    1u64 << tag_lead_index(tag)
}

#[verifier::inline]
pub open spec fn tag_lead_mask(tag: Tag) -> Asn1TagLeadMask {
    let bit = tag_lead_bit(tag);
    match tag.class {
        Class::Universal => Asn1TagLeadMask {
            universal: bit,
            application: 0,
            context_specific: 0,
            private: 0,
        },
        Class::Application => Asn1TagLeadMask {
            universal: 0,
            application: bit,
            context_specific: 0,
            private: 0,
        },
        Class::ContextSpecific => Asn1TagLeadMask {
            universal: 0,
            application: 0,
            context_specific: bit,
            private: 0,
        },
        Class::Private => Asn1TagLeadMask {
            universal: 0,
            application: 0,
            context_specific: 0,
            private: bit,
        },
    }
}

#[verifier::inline]
pub open spec fn tag_lead_masks_union(
    left: Asn1TagLeadMask,
    right: Asn1TagLeadMask,
) -> Asn1TagLeadMask {
    Asn1TagLeadMask {
        universal: left.universal | right.universal,
        application: left.application | right.application,
        context_specific: left.context_specific | right.context_specific,
        private: left.private | right.private,
    }
}

pub open spec fn tag_lead_mask_contains(mask: Asn1TagLeadMask, tag: Tag) -> bool {
    let bit = tag_lead_bit(tag);
    match tag.class {
        Class::Universal => mask.universal & bit != 0,
        Class::Application => mask.application & bit != 0,
        Class::ContextSpecific => mask.context_specific & bit != 0,
        Class::Private => mask.private & bit != 0,
    }
}

#[verifier::inline]
pub open spec fn tag_lead_masks_disjoint(left: Asn1TagLeadMask, right: Asn1TagLeadMask) -> bool {
    &&& left.universal & right.universal == 0
    &&& left.application & right.application == 0
    &&& left.context_specific & right.context_specific == 0
    &&& left.private & right.private == 0
}

pub open spec fn asn1_start_exact(tag: Tag) -> Asn1StartDomain {
    asn1_start_exact_uint(tag.class, tag.constructed, tag_num_to_uint(tag.number))
}

/// FIRST certificate for a tag whose number is kept in its numeric representation.
///
/// Generated nominal formats store their retaggable tag as `(Class, u64)`.  Keeping their
/// public certificate in that same representation avoids repeatedly normalizing through the
/// `TagNumber` enum merely to select one bitmap bit.
pub open spec fn asn1_start_exact_uint(
    class: Class,
    constructed: bool,
    number: u64,
) -> Asn1StartDomain {
    let low = if number < 31u64 {
        number
    } else {
        31u64
    };
    let index = if constructed {
        low | 32u64
    } else {
        low
    };
    let bit = 1u64 << index;
    Asn1StartDomain {
        accepts_empty: false,
        tags: match class {
            Class::Universal => Asn1TagLeadMask {
                universal: bit,
                application: 0,
                context_specific: 0,
                private: 0,
            },
            Class::Application => Asn1TagLeadMask {
                universal: 0,
                application: bit,
                context_specific: 0,
                private: 0,
            },
            Class::ContextSpecific => Asn1TagLeadMask {
                universal: 0,
                application: 0,
                context_specific: bit,
                private: 0,
            },
            Class::Private => Asn1TagLeadMask {
                universal: 0,
                application: 0,
                context_specific: 0,
                private: bit,
            },
        },
    }
}

/// Numeric and `TagNumber` singleton certificates denote the same identifier lead octet.
pub proof fn lemma_asn1_start_exact_uint(class: Class, constructed: bool, number: u64)
    ensures
        asn1_start_exact(Tag { class, constructed, number: tag_num_from_uint(number) })
            == asn1_start_exact_uint(class, constructed, number),
{
    lemma_tag_number_roundtrip(number);
}

/// Whether two numeric tags have different identifier leading octets.
pub open spec fn tag_leads_distinct_uint(
    left_class: Class,
    left_constructed: bool,
    left_number: u64,
    right_class: Class,
    right_constructed: bool,
    right_number: u64,
) -> bool {
    ||| left_class != right_class
    ||| left_constructed != right_constructed
    ||| (if left_number < 31u64 {
        left_number
    } else {
        31u64
    }) != (if right_number < 31u64 {
        right_number
    } else {
        31u64
    })
}

/// Numeric singleton certificates are disjoint exactly when their lead octets differ.
pub broadcast proof fn lemma_asn1_starts_disjoint_exact_uint(
    left_class: Class,
    left_constructed: bool,
    left_number: u64,
    right_class: Class,
    right_constructed: bool,
    right_number: u64,
)
    ensures
        #[trigger] asn1_starts_disjoint(
            asn1_start_exact_uint(left_class, left_constructed, left_number),
            asn1_start_exact_uint(right_class, right_constructed, right_number),
        ) <==> tag_leads_distinct_uint(
            left_class,
            left_constructed,
            left_number,
            right_class,
            right_constructed,
            right_number,
        ),
{
    let left = Tag {
        class: left_class,
        constructed: left_constructed,
        number: tag_num_from_uint(left_number),
    };
    let right = Tag {
        class: right_class,
        constructed: right_constructed,
        number: tag_num_from_uint(right_number),
    };
    lemma_tag_number_roundtrip(left_number);
    lemma_tag_number_roundtrip(right_number);
    lemma_asn1_start_exact_uint(left_class, left_constructed, left_number);
    lemma_asn1_start_exact_uint(right_class, right_constructed, right_number);
    lemma_asn1_starts_disjoint_exact(left, right);
}

pub open spec fn asn1_start_identity(class: Class, number: TagNumber) -> Asn1StartDomain {
    asn1_start_identity_uint(class, tag_num_to_uint(number))
}

/// FIRST certificate for either constructed bit of a numeric tag.
#[verifier::inline]
pub open spec fn asn1_start_identity_uint(class: Class, number: u64) -> Asn1StartDomain {
    asn1_start_union(
        asn1_start_exact_uint(class, false, number),
        asn1_start_exact_uint(class, true, number),
    )
}

/// Numeric and `TagNumber` identity certificates denote the same two lead octets.
pub proof fn lemma_asn1_start_identity_uint(class: Class, number: u64)
    ensures
        asn1_start_identity(class, tag_num_from_uint(number)) == asn1_start_identity_uint(
            class,
            number,
        ),
{
    lemma_asn1_start_exact_uint(class, false, number);
    lemma_asn1_start_exact_uint(class, true, number);
}

pub open spec fn asn1_start_any_non_eoc() -> Asn1StartDomain {
    Asn1StartDomain {
        accepts_empty: false,
        tags: Asn1TagLeadMask {
            universal: 0xffff_ffff_ffff_fffeu64,
            application: 0xffff_ffff_ffff_ffffu64,
            context_specific: 0xffff_ffff_ffff_ffffu64,
            private: 0xffff_ffff_ffff_ffffu64,
        },
    }
}

pub open spec fn asn1_start_ber_boundary() -> Asn1StartDomain {
    Asn1StartDomain { accepts_empty: true, tags: tag_lead_mask(TagFmt::EOC) }
}

pub open spec fn asn1_start_empty() -> Asn1StartDomain {
    Asn1StartDomain { accepts_empty: true, tags: empty_tag_lead_mask() }
}

pub open spec fn asn1_start_union(
    left: Asn1StartDomain,
    right: Asn1StartDomain,
) -> Asn1StartDomain {
    Asn1StartDomain {
        accepts_empty: left.accepts_empty || right.accepts_empty,
        tags: tag_lead_masks_union(left.tags, right.tags),
    }
}

/// Whether `input` has a start represented by `domain`.
pub open spec fn input_starts_with(input: Seq<u8>, domain: Asn1StartDomain) -> bool {
    ||| input.len() == 0 && domain.accepts_empty
    ||| match TagFmt.spec_parse(input) {
        Some((_n, tag)) => tag_lead_mask_contains(domain.tags, tag),
        None => false,
    }
}

/// A constant-size, quantifier-free sufficient test for disjoint ASN.1 FIRST domains.
pub open spec fn asn1_starts_disjoint(left: Asn1StartDomain, right: Asn1StartDomain) -> bool {
    &&& !(left.accepts_empty && right.accepts_empty)
    &&& tag_lead_masks_disjoint(left.tags, right.tags)
}

/// Whether two tags have different identifier leading octets.
///
/// All high tag numbers deliberately have index 31 within their primitive/constructed half, so
/// this predicate preserves the documented conservative high-tag behavior.
pub open spec fn tag_leads_distinct(left: Tag, right: Tag) -> bool {
    ||| left.class != right.class
    ||| left.constructed != right.constructed
    ||| tag_lead_low(left.number) != tag_lead_low(right.number)
}

/// Converting a numeric tag number to its canonical enum representation preserves its value.
pub broadcast proof fn lemma_tag_number_roundtrip(number: u64)
    ensures
        #[trigger] tag_num_to_uint(super::tag::uint_to_tag_num(number)) == number,
        #[trigger] tag_num_to_uint(tag_num_from_uint(number)) == number,
{
}

proof fn lemma_word_union_contains(left: u64, right: u64, bit: u64)
    by (bit_vector)
    requires
        left & bit != 0 || right & bit != 0,
    ensures
        (left | right) & bit != 0,
{
}

proof fn lemma_tag_lead_union_contains(left: Asn1TagLeadMask, right: Asn1TagLeadMask, tag: Tag)
    requires
        tag_lead_mask_contains(left, tag) || tag_lead_mask_contains(right, tag),
    ensures
        tag_lead_mask_contains(tag_lead_masks_union(left, right), tag),
{
    let bit = tag_lead_bit(tag);
    match tag.class {
        Class::Universal => lemma_word_union_contains(left.universal, right.universal, bit),
        Class::Application => lemma_word_union_contains(left.application, right.application, bit),
        Class::ContextSpecific => {
            lemma_word_union_contains(left.context_specific, right.context_specific, bit)
        },
        Class::Private => lemma_word_union_contains(left.private, right.private, bit),
    }
}

pub proof fn lemma_input_starts_with_union(
    input: Seq<u8>,
    left: Asn1StartDomain,
    right: Asn1StartDomain,
)
    requires
        input_starts_with(input, left) || input_starts_with(input, right),
    ensures
        input_starts_with(input, asn1_start_union(left, right)),
{
    if input.len() != 0 {
        if let Some((_n, tag)) = TagFmt.spec_parse(input) {
            lemma_tag_lead_union_contains(left.tags, right.tags, tag);
        }
    }
}

proof fn lemma_disjoint_words_cannot_contain_same_bit(left: u64, right: u64, bit_index: u64)
    by (bit_vector)
    requires
        bit_index < 64,
        left & right == 0,
        left & (1u64 << bit_index) != 0,
        right & (1u64 << bit_index) != 0,
    ensures
        false,
{
}

proof fn lemma_single_bits_disjoint(left_index: u64, right_index: u64)
    by (bit_vector)
    requires
        left_index < 64,
        right_index < 64,
    ensures
        ((1u64 << left_index) & (1u64 << right_index) == 0) <==> left_index != right_index,
{
}

proof fn lemma_tag_lead_low_bound(number: TagNumber)
    ensures
        tag_lead_low(number) < 32,
{
}

proof fn lemma_tag_lead_index_bound(tag: Tag)
    ensures
        tag_lead_index(tag) < 64,
{
    let low = tag_lead_low(tag.number);
    lemma_tag_lead_low_bound(tag.number);
    assert((low | 32u64) < 64u64) by (bit_vector)
        requires
            low < 32,
    ;
}

proof fn lemma_tag_lead_indices_distinct(left: Tag, right: Tag)
    ensures
        tag_lead_index(left) != tag_lead_index(right) <==> left.constructed != right.constructed
            || tag_lead_low(left.number) != tag_lead_low(right.number),
{
    let left_low = tag_lead_low(left.number);
    let right_low = tag_lead_low(right.number);
    lemma_tag_lead_low_bound(left.number);
    lemma_tag_lead_low_bound(right.number);
    if left.constructed {
        if right.constructed {
            assert((left_low | 32u64) != (right_low | 32u64) <==> left_low != right_low)
                by (bit_vector)
                requires
                    left_low < 32,
                    right_low < 32,
            ;
        } else {
            assert((left_low | 32u64) != right_low) by (bit_vector)
                requires
                    left_low < 32,
                    right_low < 32,
            ;
        }
    } else if right.constructed {
        assert(left_low != (right_low | 32u64)) by (bit_vector)
            requires
                left_low < 32,
                right_low < 32,
        ;
    }
}

proof fn lemma_exact_tag_lead_masks_disjoint(left: Tag, right: Tag)
    ensures
        tag_lead_masks_disjoint(tag_lead_mask(left), tag_lead_mask(right)) <==> left.class
            != right.class || tag_lead_bit(left) & tag_lead_bit(right) == 0,
{
    let left_bit = tag_lead_bit(left);
    let right_bit = tag_lead_bit(right);
    assert(left_bit & 0u64 == 0) by (bit_vector);
    assert(0u64 & right_bit == 0) by (bit_vector);
    assert(0u64 & 0u64 == 0) by (bit_vector);
}

/// Exact one-octet FIRST domains are disjoint exactly when their leading octets differ.
pub broadcast proof fn lemma_asn1_starts_disjoint_exact(left: Tag, right: Tag)
    ensures
        #[trigger] asn1_starts_disjoint(asn1_start_exact(left), asn1_start_exact(right))
            <==> tag_leads_distinct(left, right),
{
    lemma_tag_lead_index_bound(left);
    lemma_tag_lead_index_bound(right);
    lemma_tag_lead_indices_distinct(left, right);
    lemma_single_bits_disjoint(tag_lead_index(left), tag_lead_index(right));
    lemma_exact_tag_lead_masks_disjoint(left, right);
}

proof fn lemma_tag_lead_mask_contains_self(tag: Tag)
    ensures
        tag_lead_mask_contains(tag_lead_mask(tag), tag),
{
    lemma_tag_lead_index_bound(tag);
    let index = tag_lead_index(tag);
    assert((1u64 << index) & (1u64 << index) != 0) by (bit_vector)
        requires
            index < 64,
    ;
}

proof fn lemma_identity_mask_contains(class: Class, number: TagNumber, tag: Tag)
    requires
        tag.class == class,
        tag.number == number,
    ensures
        tag_lead_mask_contains(asn1_start_identity(class, number).tags, tag),
{
    lemma_tag_lead_mask_contains_self(tag);
    let primitive = Tag { class, constructed: false, number };
    let constructed = Tag { class, constructed: true, number };
    lemma_tag_lead_union_contains(tag_lead_mask(primitive), tag_lead_mask(constructed), tag);
}

proof fn lemma_exact_input_starts_with_bitmap(input: Seq<u8>, tag: Tag)
    requires
        exists|n: int| TagFmt.spec_parse(input) == Some((n, tag)),
    ensures
        input_starts_with(input, asn1_start_exact(tag)),
{
    lemma_tag_lead_mask_contains_self(tag);
}

proof fn lemma_identity_input_starts_with_bitmap(input: Seq<u8>, class: Class, number: TagNumber)
    requires
        exists|n: int, tag: Tag|
            TagFmt.spec_parse(input) == Some((n, tag)) && tag.class == class && tag.number
                == number,
    ensures
        input_starts_with(input, asn1_start_identity(class, number)),
{
    let parsed = choose|parsed: (int, Tag)|
        #![auto]
        TagFmt.spec_parse(input) == Some(parsed) && parsed.1.class == class && parsed.1.number
            == number;
    lemma_identity_mask_contains(class, number, parsed.1);
}

proof fn lemma_wf_zero_tag_number_is_eoc(number: TagNumber)
    requires
        super::tag::tag_number_wf(number),
        tag_num_to_uint(number) == 0,
    ensures
        number == TagNumber::EOC,
{
}

proof fn lemma_any_non_eoc_mask_contains(tag: Tag)
    requires
        super::tag::tag_number_wf(tag.number),
        tag != TagFmt::EOC,
    ensures
        tag_lead_mask_contains(asn1_start_any_non_eoc().tags, tag),
{
    lemma_tag_lead_index_bound(tag);
    let index = tag_lead_index(tag);
    if tag.class == Class::Universal {
        if index == 0 {
            let number = tag_num_to_uint(tag.number);
            let low = tag_lead_low(tag.number);
            if tag.constructed {
                assert(index == (low | 32u64));
                assert((low | 32u64) != 0) by (bit_vector);
            } else if number < 31u64 {
                assert(low == number);
                assert(index == number);
                lemma_wf_zero_tag_number_is_eoc(tag.number);
                assert(tag == TagFmt::EOC);
            } else {
                assert(low == 31u64);
                assert(index == 31u64);
            }
        }
        assert(0xffff_ffff_ffff_fffeu64 & (1u64 << index) != 0) by (bit_vector)
            requires
                index < 64,
                index != 0,
        ;
    } else {
        assert(0xffff_ffff_ffff_ffffu64 & (1u64 << index) != 0) by (bit_vector)
            requires
                index < 64,
        ;
    }
}

proof fn lemma_disjoint_masks_cannot_contain_same_tag(
    left: Asn1TagLeadMask,
    right: Asn1TagLeadMask,
    tag: Tag,
)
    requires
        tag_lead_masks_disjoint(left, right),
        tag_lead_mask_contains(left, tag),
        tag_lead_mask_contains(right, tag),
    ensures
        false,
{
    lemma_tag_lead_index_bound(tag);
    let index = tag_lead_index(tag);
    match tag.class {
        Class::Universal => lemma_disjoint_words_cannot_contain_same_bit(
            left.universal,
            right.universal,
            index,
        ),
        Class::Application => lemma_disjoint_words_cannot_contain_same_bit(
            left.application,
            right.application,
            index,
        ),
        Class::ContextSpecific => lemma_disjoint_words_cannot_contain_same_bit(
            left.context_specific,
            right.context_specific,
            index,
        ),
        Class::Private => lemma_disjoint_words_cannot_contain_same_bit(
            left.private,
            right.private,
            index,
        ),
    }
}

proof fn lemma_disjoint_starts_cannot_both_hold(
    input: Seq<u8>,
    left: Asn1StartDomain,
    right: Asn1StartDomain,
)
    requires
        asn1_starts_disjoint(left, right),
        input_starts_with(input, left),
        input_starts_with(input, right),
    ensures
        false,
{
    if input.len() == 0 {
    } else if let Some((_n, tag)) = TagFmt.spec_parse(input) {
        lemma_disjoint_masks_cannot_contain_same_tag(left.tags, right.tags, tag);
    }
}

/// Parsers whose accepted inputs have a compositional ASN.1 start-domain description.
pub trait HasAsn1Start: SpecParser {
    spec fn asn1_start(&self) -> Asn1StartDomain;

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>)
        ensures
            self.spec_parse(input) is Some ==> input_starts_with(input, self.asn1_start()),
    ;
}

/// A constant ASN.1 tag has the exact start domain of its required tag value.
impl HasAsn1Start for Const<TagFmt, Tag> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_exact_uint(self.1.class, self.1.constructed, tag_num_to_uint(self.1.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_exact_input_starts_with_bitmap(input, self.1);
        }
    }
}

/// Ordinary definite-length TLVs have one exact outer tag.
impl<Content: SpecCombinator, const DER: bool> HasAsn1Start for ASN1Fmt<Content, DER> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_exact_uint(self.0.class, self.0.constructed, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_exact_input_starts_with_bitmap(input, self.0);
        }
    }
}

/// BER SEQUENCE has one exact, necessarily constructed outer tag.
impl<Content: SpecCombinator> HasAsn1Start for BerSequenceFmt<Content> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_exact_uint(self.0.class, self.0.constructed, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_exact_input_starts_with_bitmap(input, self.0);
        }
    }
}

/// BER SEQUENCE OF has one exact, necessarily constructed outer tag.
impl<Content: SpecCombinator> HasAsn1Start for BerSequenceOfFmt<Content> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_exact_uint(self.0.class, self.0.constructed, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_exact_input_starts_with_bitmap(input, self.0);
        }
    }
}

/// Recursive BER OCTET STRING accepts primitive and constructed forms of one tag identity.
impl<const LIMIT: usize> HasAsn1Start for BerOctetStringFmt<LIMIT> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_identity_uint(self.0.class, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_identity_input_starts_with_bitmap(input, self.0.class, self.0.number);
        }
    }
}

/// Recursive BER BIT STRING accepts primitive and constructed forms of one tag identity.
impl<const LIMIT: usize> HasAsn1Start for BerBitStringFmt<LIMIT> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_identity_uint(self.0.class, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_identity_input_starts_with_bitmap(input, self.0.class, self.0.number);
        }
    }
}

/// BER restricted character strings inherit the primitive/constructed identity of their
/// underlying recursive OCTET STRING.
impl<Content: SpecCombinator, const LIMIT: usize> HasAsn1Start for BerCharStringFmt<
    Content,
    LIMIT,
> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_identity_uint(self.0.class, tag_num_to_uint(self.0.number))
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            lemma_identity_input_starts_with_bitmap(input, self.0.class, self.0.number);
        }
    }
}

/// Definite-length ANY accepts every complete tag except EOC.
impl<const DER: bool> HasAsn1Start for AnyFmt<DER> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_any_non_eoc()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            let parsed = choose|parsed: (int, Tag)|
                #![auto]
                TagFmt.spec_parse(input) == Some(parsed) && parsed.1 != TagFmt::EOC;
            TagFmt.lemma_parse_sound_value(input);
            lemma_any_non_eoc_mask_contains(parsed.1);
        }
    }
}

/// Recursive BER ANY accepts every complete tag except EOC.
impl<const LIMIT: usize> HasAsn1Start for BerAnyFmt<LIMIT> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_any_non_eoc()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some {
            let parsed = choose|parsed: (int, Tag)|
                #![auto]
                TagFmt.spec_parse(input) == Some(parsed) && parsed.1 != TagFmt::EOC;
            TagFmt.lemma_parse_sound_value(input);
            lemma_any_non_eoc_mask_contains(parsed.1);
        }
    }
}

/// BER_END recognizes either EOF or an EOC prefix without consuming it.
impl HasAsn1Start for BerEndFmt {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_ber_boundary()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        if self.spec_parse(input) is Some && input.len() != 0 {
            lemma_exact_input_starts_with_bitmap(input, TagFmt::EOC);
        }
    }
}

/// EOF accepts only the empty input.
impl HasAsn1Start for Eof {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_empty()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Refinement can only narrow an accepted input domain.
impl<Inner: HasAsn1Start, Predicate: SpecPred<Inner::PVal>> HasAsn1Start for Refined<
    Inner,
    Predicate,
> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.0.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
    }
}

/// Semantic mapping does not change the accepted byte domain.
impl<Inner, Mapper> HasAsn1Start for Mapped<Inner, Mapper> where
    Inner: HasAsn1Start,
    Mapper: SpecMapper<In = Inner::PVal>,
 {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.inner.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.inner.lemma_parse_implies_asn1_start(input);
    }
}

/// `BiMap` mapping does not change the accepted byte domain.
impl<Inner, Mapper, Reverse> HasAsn1Start for Mapped<Inner, BiMap<Mapper, Reverse>> where
    Inner: HasAsn1Start,
    Mapper: SpecMap<Input = Inner::PVal>,
    Reverse: SpecMap<Input = Mapper::Output, Output = Mapper::Input>,
 {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.inner.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.inner.lemma_parse_implies_asn1_start(input);
    }
}

/// Borrowing adaptation does not change the accepted byte domain.
impl<Inner: HasAsn1Start> HasAsn1Start for Ref<Inner> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.0.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
    }
}

/// Diagnostic naming does not change the accepted byte domain.
impl<Inner: HasAsn1Start> HasAsn1Start for Named<Inner> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.1.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.1.lemma_parse_implies_asn1_start(input);
    }
}

/// IMPLICIT tagging delegates parsing and its start domain to the concretely retagged format.
impl<Format> HasAsn1Start for ImplicitlyTaggedFmt<Format> where Format: Retaggable + HasAsn1Start {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.1.spec_retagged(self.0).asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.1.spec_retagged(self.0).lemma_parse_implies_asn1_start(input);
    }
}

/// A required pair starts wherever its required left component starts.
impl<Left: HasAsn1Start, Right: SpecParser> HasAsn1Start for Pair<Left, Right> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.0.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
    }
}

/// An optional field starts with either the present field or its continuation.
impl<Field: HasAsn1Start, Rest: HasAsn1Start> HasAsn1Start for Optional<Field, Rest> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_union(self.0.asn1_start(), self.1.asn1_start())
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
        self.1.lemma_parse_implies_asn1_start(input);
        if self.spec_parse(input) is Some {
            if self.0.spec_parse(input) is None {
                assert(input.skip(0) == input);
            }
            lemma_input_starts_with_union(input, self.0.asn1_start(), self.1.asn1_start());
        }
    }
}

/// ASN.1 DEFAULT has the same possible starts as OPTIONAL: the field or its continuation.
impl<Field, Rest, const DER: bool> HasAsn1Start for DefaultedFmt<
    Field,
    Field::PVal,
    Rest,
    DER,
> where
    Field: SpecByteLen + HasAsn1Start<PVal = Field::T>,
    Rest: SpecByteLen + HasAsn1Start<PVal = Rest::T>,
 {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_union(self.0.asn1_start(), self.2.asn1_start())
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        let fmt = super::modifiers::defaulted_fmt::<Field, Rest, DER>(self.0, self.1, self.2);
        fmt.lemma_parse_implies_asn1_start(input);
    }
}

/// A structural choice accepts the union of the starts accepted by either branch.
impl<Left: HasAsn1Start, Right: HasAsn1Start> HasAsn1Start for Choice<Left, Right> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_union(self.0.asn1_start(), self.1.asn1_start())
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
        self.1.lemma_parse_implies_asn1_start(input);
        if self.spec_parse(input) is Some {
            lemma_input_starts_with_union(input, self.0.asn1_start(), self.1.asn1_start());
        }
    }
}

/// Ordered alternatives have the same accepted start union as structural choices.
impl<
    const NONDETERMINISTIC: bool,
    Left: HasAsn1Start,
    Right: HasAsn1Start<PVal = Left::PVal>,
> HasAsn1Start for Alt<Left, Right, NONDETERMINISTIC> {
    #[verifier::inline]
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        asn1_start_union(self.0.asn1_start(), self.1.asn1_start())
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
        self.1.lemma_parse_implies_asn1_start(input);
        if self.spec_parse(input) is Some {
            lemma_input_starts_with_union(input, self.0.asn1_start(), self.1.asn1_start());
        }
    }
}

/// Key lemma: Disjoint ASN.1 start domains imply disjoint parser domains.
///
/// The theorem remains directly callable so generated code need not depend on quantifier-trigger
/// discovery. Its single directional trigger is also useful for small hand-written formats.
pub broadcast proof fn lemma_disjoint_asn1_starts<Left: HasAsn1Start, Right: HasAsn1Start>(
    left: Left,
    right: Right,
)
    requires
        asn1_starts_disjoint(left.asn1_start(), right.asn1_start()),
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
    assert forall|input: Seq<u8>|
        left.spec_parse(input) is Some && right.spec_parse(input) is Some implies false by {
        left.lemma_parse_implies_asn1_start(input);
        right.lemma_parse_implies_asn1_start(input);
        lemma_disjoint_starts_cannot_both_hold(input, left.asn1_start(), right.asn1_start());
    }
}

/// A defaulted field can start either at the field itself or at its continuation.
///
/// This structural rule complements the bitmap leaf rule: it lets ordinary combinator
/// automation reduce a DEFAULT chain without asking the SMT solver to evaluate bitwise
/// operations itself.
pub broadcast proof fn lemma_disjoint_defaulted<Parser, Field, Rest, const DER: bool>(
    parser: Parser,
    defaulted: DefaultedFmt<Field, Field::PVal, Rest, DER>,
) where
    Parser: SpecParser,
    Field: SpecByteLen + SpecParser<PVal = Field::T>,
    Rest: SpecByteLen + SpecParser<PVal = Rest::T>,

    requires
        disjoint_domains(parser, defaulted.0),
        disjoint_domains(parser, defaulted.2),
    ensures
        #[trigger] disjoint_domains(parser, defaulted),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// Small ASN.1-specific automation group for handwritten backend formats. Generated schemas use
/// explicit local FIRST-set certificates instead of relying on global quantifier saturation.
pub broadcast group asn1_disjointness_lemmas {
    lemma_tag_number_roundtrip,
    lemma_asn1_starts_disjoint_exact,
    lemma_asn1_starts_disjoint_exact_uint,
    lemma_disjoint_asn1_starts,
    lemma_disjoint_defaulted,
}

} // verus!
