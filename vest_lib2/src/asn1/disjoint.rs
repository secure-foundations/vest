//! Compositional disjointness proofs for complete ASN.1 formats.
//!
//! Broadcast automation in this module is intentionally small: each complete ASN.1 format
//! exposes an over-approximation of what can occur at the start of an accepted input, and one
//! generic theorem turns disjoint start domains into [`disjoint_domains`]. Adding another ASN.1
//! format therefore needs one start-domain proof rather than pairwise proofs against every
//! existing format.
use super::ber::*;
use super::modifiers::{DefaultedFmt, ImplicitlyTaggedFmt, Retaggable};
use super::tag::TagNumber;
use super::{ASN1Fmt, AnyFmt, Class, Tag, TagFmt};
use crate::combinators::mapped::spec::{BiMap, SpecMap, SpecMapper};
use crate::combinators::{Const, Mapped, Named, Ref, Refined};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

/// A compact over-approximation of what may occur at the start of an accepted ASN.1 input.
///
/// `Identity` deliberately ignores the constructed bit. It is used by BER string formats whose
/// primitive and constructed encodings share a class and tag number. `BerBoundary` describes the
/// zero-width [`BerEndFmt`] lookahead: end of input or an EOC prefix.
#[derive(StructuralEq, Clone, Copy, PartialEq, Eq)]
#[verifier::ext_equal]
pub enum Asn1StartDomain {
    Exact(Tag),
    Identity { class: Class, number: TagNumber },
    AnyNonEoc,
    BerBoundary,
}

/// Whether `input` has a start represented by `domain`.
///
/// This predicate is an over-approximation. In particular, `BerBoundary` only records the EOC tag
/// prefix; [`BerEndFmt`] additionally checks the zero length octet.
pub open spec fn input_starts_with(input: Seq<u8>, domain: Asn1StartDomain) -> bool {
    match domain {
        Asn1StartDomain::Exact(expected) => {
            exists|n: int| TagFmt.spec_parse(input) == Some((n, expected))
        },
        Asn1StartDomain::Identity { class, number } => {
            exists|n: int, tag: Tag|
                TagFmt.spec_parse(input) == Some((n, tag)) && tag.class == class && tag.number
                    == number
        },
        Asn1StartDomain::AnyNonEoc => {
            exists|n: int, tag: Tag|
                TagFmt.spec_parse(input) == Some((n, tag)) && tag != TagFmt::EOC
        },
        Asn1StartDomain::BerBoundary => {
            input.len() == 0 || exists|n: int| TagFmt.spec_parse(input) == Some((n, TagFmt::EOC))
        },
    }
}

/// A quantifier-free test sufficient to show that two ASN.1 start domains do not overlap.
pub open spec fn asn1_starts_disjoint(left: Asn1StartDomain, right: Asn1StartDomain) -> bool {
    match left {
        Asn1StartDomain::Exact(left_tag) => match right {
            Asn1StartDomain::Exact(right_tag) => left_tag != right_tag,
            Asn1StartDomain::Identity { class, number } => {
                left_tag.class != class || left_tag.number != number
            },
            Asn1StartDomain::AnyNonEoc => left_tag == TagFmt::EOC,
            Asn1StartDomain::BerBoundary => left_tag != TagFmt::EOC,
        },
        Asn1StartDomain::Identity { class: left_class, number: left_number } => match right {
            Asn1StartDomain::Exact(right_tag) => {
                left_class != right_tag.class || left_number != right_tag.number
            },
            Asn1StartDomain::Identity { class: right_class, number: right_number } => {
                left_class != right_class || left_number != right_number
            },
            // Even the EOC identity contains the constructed form, which is a non-EOC tag.
            Asn1StartDomain::AnyNonEoc => false,
            Asn1StartDomain::BerBoundary => {
                left_class != TagFmt::EOC.class || left_number != TagFmt::EOC.number
            },
        },
        Asn1StartDomain::AnyNonEoc => match right {
            Asn1StartDomain::Exact(right_tag) => right_tag == TagFmt::EOC,
            Asn1StartDomain::Identity { .. } => false,
            Asn1StartDomain::AnyNonEoc => false,
            Asn1StartDomain::BerBoundary => true,
        },
        Asn1StartDomain::BerBoundary => match right {
            Asn1StartDomain::Exact(right_tag) => right_tag != TagFmt::EOC,
            Asn1StartDomain::Identity { class, number } => {
                class != TagFmt::EOC.class || number != TagFmt::EOC.number
            },
            Asn1StartDomain::AnyNonEoc => true,
            Asn1StartDomain::BerBoundary => false,
        },
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
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Exact(self.1)
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Ordinary definite-length TLVs have one exact outer tag.
impl<Content: SpecCombinator, const DER: bool> HasAsn1Start for ASN1Fmt<Content, DER> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Exact(self.0)
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// BER SEQUENCE has one exact, necessarily constructed outer tag.
impl<Content: SpecCombinator> HasAsn1Start for BerSequenceFmt<Content> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Exact(self.0)
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// BER SEQUENCE OF has one exact, necessarily constructed outer tag.
impl<Content: SpecCombinator> HasAsn1Start for BerSequenceOfFmt<Content> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Exact(self.0)
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Recursive BER OCTET STRING accepts primitive and constructed forms of one tag identity.
impl<const LIMIT: usize> HasAsn1Start for BerOctetStringFmt<LIMIT> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Identity { class: self.0.class, number: self.0.number }
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Recursive BER BIT STRING accepts primitive and constructed forms of one tag identity.
impl<const LIMIT: usize> HasAsn1Start for BerBitStringFmt<LIMIT> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Identity { class: self.0.class, number: self.0.number }
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// BER restricted character strings inherit the primitive/constructed identity of their
/// underlying recursive OCTET STRING.
impl<Content: SpecCombinator, const LIMIT: usize> HasAsn1Start for BerCharStringFmt<
    Content,
    LIMIT,
> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::Identity { class: self.0.class, number: self.0.number }
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Definite-length ANY accepts every complete tag except EOC.
impl<const DER: bool> HasAsn1Start for AnyFmt<DER> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::AnyNonEoc
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Recursive BER ANY accepts every complete tag except EOC.
impl<const LIMIT: usize> HasAsn1Start for BerAnyFmt<LIMIT> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::AnyNonEoc
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// BER_END recognizes either EOF or an EOC prefix without consuming it.
impl HasAsn1Start for BerEndFmt {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        Asn1StartDomain::BerBoundary
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
    }
}

/// Refinement can only narrow an accepted input domain.
impl<Inner: HasAsn1Start, Predicate: SpecPred<Inner::PVal>> HasAsn1Start for Refined<
    Inner,
    Predicate,
> {
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
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.inner.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.inner.lemma_parse_implies_asn1_start(input);
    }
}

/// Borrowing adaptation does not change the accepted byte domain.
impl<Inner: HasAsn1Start> HasAsn1Start for Ref<Inner> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.0.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.0.lemma_parse_implies_asn1_start(input);
    }
}

/// Diagnostic naming does not change the accepted byte domain.
impl<Inner: HasAsn1Start> HasAsn1Start for Named<Inner> {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.1.asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.1.lemma_parse_implies_asn1_start(input);
    }
}

/// IMPLICIT tagging delegates parsing and its start domain to the concretely retagged format.
impl<Format> HasAsn1Start for ImplicitlyTaggedFmt<Format> where Format: Retaggable + HasAsn1Start {
    open spec fn asn1_start(&self) -> Asn1StartDomain {
        self.1.spec_retagged(self.0).asn1_start()
    }

    proof fn lemma_parse_implies_asn1_start(&self, input: Seq<u8>) {
        self.1.spec_retagged(self.0).lemma_parse_implies_asn1_start(input);
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
    }
}

/// A defaulted parser is disjoint from another parser if both possible starts are.
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

/// Reverse-orientation defaulted decomposition for explicitly left-associated formats.
pub broadcast proof fn lemma_disjoint_defaulted_left<Parser, Field, Rest, const DER: bool>(
    defaulted: DefaultedFmt<Field, Field::PVal, Rest, DER>,
    parser: Parser,
) where
    Parser: SpecParser,
    Field: SpecByteLen + SpecParser<PVal = Field::T>,
    Rest: SpecByteLen + SpecParser<PVal = Rest::T>,

    requires
        disjoint_domains(defaulted.0, parser),
        disjoint_domains(defaulted.2, parser),
    ensures
        #[trigger] disjoint_domains(defaulted, parser),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// Leaf and canonical modifier automation for ASN.1 formats.
pub broadcast group asn1_disjointness_lemmas {
    lemma_disjoint_asn1_starts,
    lemma_disjoint_defaulted,
}

/// Reverse-orientation ASN.1 decomposition, kept opt-in to avoid competing trigger paths.
pub broadcast group asn1_left_disjointness_lemmas {
    lemma_disjoint_defaulted_left,
}

#[cfg(verus_only)]
proof fn test_asn1_start_disjointness() {
    use crate::combinators::U8;

    broadcast use crate::combinators::disjoint::disjointness_lemmas;
    broadcast use asn1_disjointness_lemmas;

    let boolean = ASN1Fmt::<_, true>(TagFmt::BOOLEAN, U8);
    let octets = BerOctetStringFmt::<4>(TagFmt::OCTET_STRING);
    let bits = BerBitStringFmt::<4>(TagFmt::BIT_STRING);
    assert(asn1_starts_disjoint(boolean.asn1_start(), octets.asn1_start()));
    assert(disjoint_domains(boolean, octets));
    assert(asn1_starts_disjoint(octets.asn1_start(), bits.asn1_start()));
    assert(disjoint_domains(octets, bits));

    let wrapped = ImplicitlyTaggedFmt(
        Tag {
            class: Class::ContextSpecific,
            constructed: false,
            number: TagNumber::Other { tag_num: 7 },
        },
        Ref(Refined(octets, super::Size::<true, 0, true, 8>)),
    );
    let sequence = BerSequenceFmt(
        Tag {
            class: Class::ContextSpecific,
            constructed: true,
            number: TagNumber::Other { tag_num: 8 },
        },
        U8,
    );
    assert(asn1_starts_disjoint(wrapped.asn1_start(), sequence.asn1_start()));
    assert(disjoint_domains(wrapped, sequence));

    let same_identity = BerCharStringFmt::<_, 4>(TagFmt::OCTET_STRING, U8);
    assert(!asn1_starts_disjoint(octets.asn1_start(), same_identity.asn1_start()));

    let any = AnyFmt::<false>;
    assert(asn1_starts_disjoint(any.asn1_start(), BER_END.asn1_start()));
    assert(disjoint_domains(any, BER_END));

    assert(disjoint_domains(boolean, EOC));
}

} // verus!
