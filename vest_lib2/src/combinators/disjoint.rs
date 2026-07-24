//! Broadcast lemmas establishing [`disjoint_domains`](crate::core::spec::disjoint_domains)
//! for common combinator compositions.
use super::mapped::spec::{BiMap, SpecMap, SpecMapper};
use super::*;
use crate::core::proof::*;
use crate::core::spec::SpecPred;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

/// Two [`Const`] parsers with the same inner parser but different values are disjoint.
pub broadcast proof fn lemma_disjoint_const<Inner: SpecParser>(
    tag1: Const<Inner, Inner::PVal>,
    tag2: Const<Inner, Inner::PVal>,
)
    requires
        tag1.0 == tag2.0,
        tag1.1 != tag2.1,
    ensures
        #[trigger] disjoint_domains(tag1, tag2),
{
    reveal(disjoint_domains);
}

/// Two [`WithPrefixTag`] parsers with the same tag parser but different values are disjoint.
pub broadcast proof fn lemma_disjoint_prefix_tagged<
    Tg: SpecByteLen + SpecParser<PVal = Tg::T>,
    A: SpecParser,
    B: SpecParser,
>(prefix1: PrefixTagged<Tg, Tg::T, A>, prefix2: PrefixTagged<Tg, Tg::T, B>)
    requires
        prefix1.0 == prefix2.0,
        prefix1.1 != prefix2.1,
    ensures
        #[trigger] disjoint_domains(prefix1, prefix2),
{
    reveal(disjoint_domains);
}

/// Two [`Refined`] parsers with the same inner parser and mutually exclusive predicates are disjoint.
pub broadcast proof fn lemma_disjoint_refined<
    Inner: SpecParser,
    P1: SpecPred<Inner::PVal>,
    P2: SpecPred<Inner::PVal>,
>(r1: Refined<Inner, P1>, r2: Refined<Inner, P2>)
    requires
        r1.0 == r2.0,
        forall|v: Inner::PVal| r1.1.apply(v) ==> !r2.1.apply(v),
    ensures
        #[trigger] disjoint_domains(r1, r2),
{
    reveal(disjoint_domains);
}

/// Refining the left parser can only narrow its accepted byte domain.
pub broadcast proof fn lemma_disjoint_refined_left<
    Inner: SpecParser,
    Pred: SpecPred<Inner::PVal>,
    Other: SpecParser,
>(refined: Refined<Inner, Pred>, other: Other)
    requires
        disjoint_domains(refined.0, other),
    ensures
        #[trigger] disjoint_domains(refined, other),
{
    reveal(disjoint_domains);
}

/// Refining the right parser can only narrow its accepted byte domain.
pub broadcast proof fn lemma_disjoint_refined_right<
    Other: SpecParser,
    Inner: SpecParser,
    Pred: SpecPred<Inner::PVal>,
>(other: Other, refined: Refined<Inner, Pred>)
    requires
        disjoint_domains(other, refined.0),
    ensures
        #[trigger] disjoint_domains(other, refined),
{
    reveal(disjoint_domains);
}

/// A [`Const`] parser is disjoint from a [`Refined`] parser with the same inner parser if the refined predicate does not hold on the const value.
pub broadcast proof fn lemma_disjoint_const_refined<Inner: SpecParser, P: SpecPred<Inner::PVal>>(
    tag: Const<Inner, Inner::PVal>,
    r: Refined<Inner, P>,
)
    requires
        tag.0 == r.0,
        !r.1.apply(tag.1),
    ensures
        #[trigger] disjoint_domains(tag, r),
{
    reveal(disjoint_domains);
}

/// Two [`Cond`] parsers with mutually exclusive conditions are disjoint.
pub broadcast proof fn lemma_disjoint_cond<Inner1: SpecParser, Inner2: SpecParser>(
    c1: Cond<Inner1>,
    c2: Cond<Inner2>,
)
    requires
        c1.0 && c2.0 ==> false,
    ensures
        #[trigger] disjoint_domains(c1, c2),
{
    reveal(disjoint_domains);
}

/// A tuple parser is disjoint from another parser if its first component is.
pub broadcast proof fn lemma_disjoint_tuple<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    t: U,
    t1: Pair<U1, V1>,
)
    requires
        disjoint_domains(t, t1.0),
    ensures
        #[trigger] disjoint_domains(t, t1),
{
    reveal(disjoint_domains);
}

/// Two tuples are disjoint if their first parsers consume equal bytes and their second parsers are disjoint.
pub broadcast proof fn lemma_disjoint_tuple_2<
    A: SpecParser,
    B: SpecParser,
    C: SpecParser,
    D: SpecParser,
>(t1: Pair<A, B>, t2: Pair<C, D>)
    requires
        forall|input: Seq<u8>| #[trigger]
            t1.0.spec_parse(input) matches Some((n1, _)) ==> t2.0.spec_parse(input) matches Some(
                (n2, _),
            ) ==> n1 == n2,
        disjoint_domains(t1.1, t2.1),
    ensures
        #[trigger] disjoint_domains(t1, t2),
{
    reveal(disjoint_domains);
}

/// A [`Preceded`] parser is disjoint from another parser if its prefix is.
pub broadcast proof fn lemma_disjoint_preceded<
    U: SpecParser,
    U1: SpecParser,
    V1: SpecParser,
    const CHECK: bool,
>(p: U, p1: Preceded<U1, U1::PVal, V1, CHECK>)
    requires
        disjoint_domains(p, p1.a),
    ensures
        #[trigger] disjoint_domains(p, p1),
{
    reveal(disjoint_domains);
}

/// A [`Terminated`] parser is disjoint from another parser if its prefix is.
pub broadcast proof fn lemma_disjoint_terminated<
    U: SpecParser,
    U1: SpecParser,
    V1: SpecParser,
    const CHECK: bool,
>(p: U, p1: Terminated<U1, V1, V1::PVal, CHECK>)
    requires
        disjoint_domains(p, p1.a),
    ensures
        #[trigger] disjoint_domains(p, p1),
{
    reveal(disjoint_domains);
}

/// A [`Mapped`] parser is disjoint from another parser if its inner parser is.
pub broadcast proof fn lemma_disjoint_mapped<
    P: SpecParser,
    Inner1: SpecParser,
    M1: SpecMapper<In = Inner1::PVal>,
>(p: P, m: Mapped<Inner1, M1>)
    requires
        disjoint_domains(p, m.inner),
    ensures
        #[trigger] disjoint_domains(p, m),
{
    reveal(disjoint_domains);
}

/// A [`Mapped`] parser is disjoint from another parser if its inner parser is.
pub broadcast proof fn lemma_disjoint_mapped_left<
    Inner: SpecParser,
    M: SpecMapper<In = Inner::PVal>,
    P: SpecParser,
>(mapped: Mapped<Inner, M>, other: P)
    requires
        disjoint_domains(mapped.inner, other),
    ensures
        #[trigger] disjoint_domains(mapped, other),
{
    reveal(disjoint_domains);
}

/// A bidirectionally [`Mapped`] parser is disjoint from another parser if its inner parser is.
pub broadcast proof fn lemma_disjoint_bimap<
    P: SpecParser,
    Inner: SpecParser,
    M: SpecMap<Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,
>(other: P, mapped: Mapped<Inner, BiMap<M, MRev>>)
    requires
        disjoint_domains(other, mapped.inner),
    ensures
        #[trigger] disjoint_domains(other, mapped),
{
    reveal(disjoint_domains);
}

/// A bidirectionally [`Mapped`] parser is disjoint from another parser if its inner parser is.
pub broadcast proof fn lemma_disjoint_bimap_left<
    Inner: SpecParser,
    M: SpecMap<Input = Inner::PVal>,
    MRev: SpecMap<Input = M::Output, Output = M::Input>,
    P: SpecParser,
>(mapped: Mapped<Inner, BiMap<M, MRev>>, other: P)
    requires
        disjoint_domains(mapped.inner, other),
    ensures
        #[trigger] disjoint_domains(mapped, other),
{
    reveal(disjoint_domains);
}

/// A [`Choice`] parser is disjoint from another parser if both branches are.
///
/// ## NOTE
///
/// The trigger `disjoint_domains(other, choice)` matches `Choice(..., Choice(..., ...))` but not `Choice(Choice(..., ...), ...)`.
pub broadcast proof fn lemma_disjoint_choice<S1: SpecParser, S2: SpecParser, S3: SpecParser>(
    choice: Choice<S1, S2>,
    other: S3,
)
    requires
        disjoint_domains(other, choice.0),
        disjoint_domains(other, choice.1),
    ensures
        #[trigger] disjoint_domains(other, choice),
{
    reveal(disjoint_domains);
}

/// An [`Alt`] parser is disjoint from another parser if both branches are.
///
/// ## NOTE
///
/// The trigger `disjoint_domains(other, choice)` matches `Alt(..., Alt(..., ...))` but not `Alt(Alt(..., ...), ...)`.
pub broadcast proof fn lemma_disjoint_alt<
    S1: SpecParser,
    S2: SpecParser<PVal = S1::PVal>,
    S3: SpecParser<PVal = S1::PVal>,
>(alt: Alt<S1, S2>, other: S3)
    requires
        disjoint_domains(other, alt.0),
        disjoint_domains(other, alt.1),
    ensures
        #[trigger] disjoint_domains(other, alt),
{
    reveal(disjoint_domains);
}

/// An [`Optional<A, B>`] parser is disjoint from another parser if both `A` and `B` are.
pub broadcast proof fn lemma_disjoint_optional<P: SpecParser, A: SpecParser, B: SpecParser>(
    p: P,
    optional: Optional<A, B>,
)
    requires
        disjoint_domains(p, optional.0),
        disjoint_domains(p, optional.1),
    ensures
        #[trigger] disjoint_domains(p, optional),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// A [`Repeat<A, B>`] parser is disjoint from another parser if both `A` and `B` are.
pub broadcast proof fn lemma_disjoint_repeat<P: SpecParser, A: SpecParser, B: SpecParser>(
    p: P,
    repeat: Repeat<A, B>,
)
    requires
        disjoint_domains(p, repeat.0),
        disjoint_domains(p, repeat.1),
    ensures
        #[trigger] disjoint_domains(p, repeat),
{
    reveal(<super::Star::<_> as SpecParser>::spec_parse);
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// A productive parser is disjoint from [`Eof`].
pub broadcast proof fn lemma_disjoint_eof<P: Productive>(p: P, eof: Eof)
    requires
        p.productive_inv(),
        p.safe_inv(),
    ensures
        #[trigger] disjoint_domains(p, eof),
{
    reveal(disjoint_domains);
    assert forall|input: Seq<u8>|
        #![auto]
        p.spec_parse(input) is Some && eof.spec_parse(input) is Some implies false by {
        p.lemma_productive(input);
        p.lemma_parse_safe(input);
        if eof.spec_parse(input) is Some {
            assert(input.len() == 0);
            assert(input == Seq::<u8>::empty());
        }
    }
}

/// An [`OptionalEnd<A>`] parser is disjoint from another parser if its inner parser is
/// - productive and safe, and
/// - disjoint from the other parser.
pub broadcast proof fn lemma_disjoint_option_end<P: Productive, A: SpecParser>(
    p: P,
    opt: OptionalEnd<A>,
)
    requires
        p.productive_inv(),
        p.safe_inv(),
        disjoint_domains(p, opt.0),
    ensures
        #[trigger] disjoint_domains(p, opt),
{
    reveal(disjoint_domains);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

    assert forall|input: Seq<u8>|
        #![auto]
        p.spec_parse(input) is Some && Eof.spec_parse(input) is Some implies false by {
        p.lemma_productive(input);
        p.lemma_parse_safe(input);
    }
}

/// A [`RepeatTillEnd<A>`] parser is disjoint from another parser if its inner parser is
/// - productive and safe, and
/// - disjoint from the other parser.
pub broadcast proof fn lemma_disjoint_repeat_till_end<P: Productive, A: SpecParser>(
    p: P,
    repeat: RepeatTillEnd<A>,
)
    requires
        p.productive_inv(),
        p.safe_inv(),
        disjoint_domains(p, repeat.0),
    ensures
        #[trigger] disjoint_domains(p, repeat),
{
    reveal(disjoint_domains);
    reveal(<super::Star::<_> as SpecParser>::spec_parse);
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

    assert forall|input: Seq<u8>|
        #![auto]
        p.spec_parse(input) is Some && Eof.spec_parse(input) is Some implies false by {
        p.lemma_productive(input);
        p.lemma_parse_safe(input);
    }
}

/// Borrowing adaptation does not change a parser's accepted byte domain.
pub broadcast proof fn lemma_disjoint_ref_left<Inner: SpecParser, Other: SpecParser>(
    borrowed: Ref<Inner>,
    other: Other,
)
    requires
        disjoint_domains(borrowed.0, other),
    ensures
        #[trigger] disjoint_domains(borrowed, other),
{
    reveal(disjoint_domains);
}

/// Borrowing adaptation does not change a parser's accepted byte domain.
pub broadcast proof fn lemma_disjoint_ref_right<Other: SpecParser, Inner: SpecParser>(
    other: Other,
    borrowed: Ref<Inner>,
)
    requires
        disjoint_domains(other, borrowed.0),
    ensures
        #[trigger] disjoint_domains(other, borrowed),
{
    reveal(disjoint_domains);
}

/// Two borrowing adapters are disjoint whenever their underlying parsers are.
pub broadcast proof fn lemma_disjoint_refs<Left: SpecParser, Right: SpecParser>(
    left: Ref<Left>,
    right: Ref<Right>,
)
    requires
        disjoint_domains(left.0, right.0),
    ensures
        #[trigger] disjoint_domains(left, right),
{
    reveal(disjoint_domains);
}

pub broadcast group disjointness_lemmas {
    lemma_disjoint_choice,
    lemma_disjoint_alt,
    lemma_disjoint_const,
    lemma_disjoint_prefix_tagged,
    lemma_disjoint_refined,
    lemma_disjoint_refined_left,
    lemma_disjoint_refined_right,
    lemma_disjoint_const_refined,
    lemma_disjoint_cond,
    lemma_disjoint_tuple,
    lemma_disjoint_tuple_2,
    lemma_disjoint_preceded,
    lemma_disjoint_terminated,
    lemma_disjoint_mapped,
    lemma_disjoint_mapped_left,
    lemma_disjoint_bimap,
    lemma_disjoint_bimap_left,
    lemma_disjoint_optional,
    lemma_disjoint_repeat,
    lemma_disjoint_eof,
    lemma_disjoint_option_end,
    lemma_disjoint_repeat_till_end,
    lemma_disjoint_ref_left,
    lemma_disjoint_ref_right,
    lemma_disjoint_refs,
}

#[cfg(verus_only)]
proof fn test_disjoinness() {
    use crate::combinators::*;
    use crate::core::proof::*;
    broadcast use disjointness_lemmas;

    use vstd::pervasive::arbitrary;

    let fmt = Choice(Const(U8, 0), Choice(Const(U8, 1), Choice(Const(U8, 2), Const(U8, 3))));
    assert(fmt.unambiguous());
    let fmt2 = Choice(
        Refined(U8, |b: u8| b == 0),
        Choice(
            Refined(U8, |b: u8| b == 1),
            Choice(Refined(U8, |b: u8| b == 2), Refined(U8, |b: u8| b == 3)),
        ),
    );
    assert(fmt2.unambiguous());
    let tag: u8 = arbitrary();
    let fmt3 = Choice(
        Cond(tag == 0, U8),
        Choice(Cond(tag == 1, U8), Choice(Cond(tag == 2, U8), Cond(tag == 3, U8))),
    );
    assert(fmt3.unambiguous());
    let fmt4 = Choice(
        Const(U8, 0),
        Choice(Const(U8, 1), Choice(Const(U8, 2), Refined(U8, |b: u8| b != 0 && b != 1 && b != 2))),
    );
    assert(fmt4.unambiguous());
    let fmt5 = Optional(
        PrefixTagged(U8, 10, Fixed::<1>),
        Repeat(
            PrefixTagged(U8, 11, Fixed::<2>),
            Optional(
                PrefixTagged(U8, 12, Fixed::<3>),
                RepeatTillEnd(PrefixTagged(U8, 13, Fixed::<4>)),
            ),
        ),
    );
    assert(fmt5.unambiguous());
}

} // verus!
