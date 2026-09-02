//! Broadcast lemmas establishing `disjoint_domains`
//! for common combinator compositions.
use super::mapped::spec::{BiMap, SpecMap, SpecMapper};
use super::*;
use crate::core::proof::*;
use crate::core::spec::SpecPred;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

/// Disjointness is symmetric, but symmetry is deliberately not broadcast: broadcasting it
/// creates a quantifier-instantiation cycle with every directional decomposition rule below.
pub proof fn lemma_disjoint_symmetric<Left: SpecParser, Right: SpecParser>(left: Left, right: Right)
    requires
        disjoint_domains(left, right),
    ensures
        disjoint_domains(right, left),
{
    reveal(disjoint_domains);
}

/// [`Void`] accepts no input and is therefore disjoint from every parser.
pub broadcast proof fn lemma_disjoint_void_left<Other: SpecParser>(void: Void, other: Other)
    ensures
        #[trigger] disjoint_domains(void, other),
{
    reveal(disjoint_domains);
}

/// Every parser is disjoint from [`Void`].
pub broadcast proof fn lemma_disjoint_void_right<Other: SpecParser>(other: Other, void: Void)
    ensures
        #[trigger] disjoint_domains(other, void),
{
    reveal(disjoint_domains);
}

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

/// Two [`PrefixTagged`](crate::combinators::PrefixTagged) parsers with the same tag parser but different values are disjoint.
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

/// A tuple parser is disjoint from another parser if its first component is.
pub broadcast proof fn lemma_disjoint_tuple_left<U1: SpecParser, V1: SpecParser, U: SpecParser>(
    tuple: Pair<U1, V1>,
    other: U,
)
    requires
        disjoint_domains(tuple.0, other),
    ensures
        #[trigger] disjoint_domains(tuple, other),
{
    reveal(disjoint_domains);
}

/// A dependent tuple is disjoint from another parser if its head parser is.
pub broadcast proof fn lemma_disjoint_bind<
    U: SpecParser,
    Head: SpecParser,
    Tail: SpecMap<Input = Head::PVal>,
>(other: U, bind: Bind<Head, Tail>) where Tail::Output: SpecParser
    requires
        disjoint_domains(other, bind.0),
    ensures
        #[trigger] disjoint_domains(other, bind),
{
    reveal(disjoint_domains);
}

/// A dependent tuple is disjoint from another parser if its head parser is.
pub broadcast proof fn lemma_disjoint_bind_left<
    Head: SpecParser,
    Tail: SpecMap<Input = Head::PVal>,
    U: SpecParser,
>(bind: Bind<Head, Tail>, other: U) where Tail::Output: SpecParser
    requires
        disjoint_domains(bind.0, other),
    ensures
        #[trigger] disjoint_domains(bind, other),
{
    reveal(disjoint_domains);
}

/// An implicit dependent parser is disjoint from another parser if its head parser is.
pub broadcast proof fn lemma_disjoint_implicit<
    U: SpecParser,
    Head: SpecParser,
    Tail: DepCombinator<Key = Head::PVal>,
>(other: U, implicit: Implicit<Head, Tail>) where Tail::Body: SpecParser<PVal = Tail::Val>
    requires
        disjoint_domains(other, implicit.0),
    ensures
        #[trigger] disjoint_domains(other, implicit),
{
    reveal(disjoint_domains);
}

/// An implicit dependent parser is disjoint from another parser if its head parser is.
pub broadcast proof fn lemma_disjoint_implicit_left<
    Head: SpecParser,
    Tail: DepCombinator<Key = Head::PVal>,
    U: SpecParser,
>(implicit: Implicit<Head, Tail>, other: U) where Tail::Body: SpecParser<PVal = Tail::Val>
    requires
        disjoint_domains(implicit.0, other),
    ensures
        #[trigger] disjoint_domains(implicit, other),
{
    reveal(disjoint_domains);
}

/// An [`AndThen`] parser is disjoint from another parser if its byte-source parser is.
pub broadcast proof fn lemma_disjoint_and_then<
    U: SpecParser,
    Head: SpecParser<PVal = Seq<u8>>,
    Tail: SpecParser,
>(other: U, and_then: AndThen<Head, Tail>)
    requires
        disjoint_domains(other, and_then.0),
    ensures
        #[trigger] disjoint_domains(other, and_then),
{
    reveal(disjoint_domains);
}

/// An [`AndThen`] parser is disjoint from another parser if its byte-source parser is.
pub broadcast proof fn lemma_disjoint_and_then_left<
    Head: SpecParser<PVal = Seq<u8>>,
    Tail: SpecParser,
    U: SpecParser,
>(and_then: AndThen<Head, Tail>, other: U)
    requires
        disjoint_domains(and_then.0, other),
    ensures
        #[trigger] disjoint_domains(and_then, other),
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

/// A [`Preceded`] parser is disjoint from another parser if its prefix is.
pub broadcast proof fn lemma_disjoint_preceded_left<
    U1: SpecParser,
    V1: SpecParser,
    U: SpecParser,
    const CHECK: bool,
>(preceded: Preceded<U1, U1::PVal, V1, CHECK>, other: U)
    requires
        disjoint_domains(preceded.a, other),
    ensures
        #[trigger] disjoint_domains(preceded, other),
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

/// A [`Terminated`] parser is disjoint from another parser if its content parser is.
pub broadcast proof fn lemma_disjoint_terminated_left<
    U1: SpecParser,
    V1: SpecParser,
    U: SpecParser,
    const CHECK: bool,
>(terminated: Terminated<U1, V1, V1::PVal, CHECK>, other: U)
    requires
        disjoint_domains(terminated.a, other),
    ensures
        #[trigger] disjoint_domains(terminated, other),
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

/// A [`Choice`] parser is disjoint from another parser if both branches are.
pub broadcast proof fn lemma_disjoint_choice_left<S1: SpecParser, S2: SpecParser, S3: SpecParser>(
    choice: Choice<S1, S2>,
    other: S3,
)
    requires
        disjoint_domains(choice.0, other),
        disjoint_domains(choice.1, other),
    ensures
        #[trigger] disjoint_domains(choice, other),
{
    reveal(disjoint_domains);
}

/// Two balanced [`Choice`] trees are disjoint if every cross-branch pair is disjoint.
///
/// Unlike composing the two directional decomposition rules, this rule strictly reduces both
/// visible choice constructors and therefore does not introduce a trigger cycle.
pub broadcast proof fn lemma_disjoint_choices<
    A: SpecParser,
    B: SpecParser,
    C: SpecParser,
    D: SpecParser,
>(left: Choice<A, B>, right: Choice<C, D>)
    requires
        disjoint_domains(left.0, right.0),
        disjoint_domains(left.0, right.1),
        disjoint_domains(left.1, right.0),
        disjoint_domains(left.1, right.1),
    ensures
        #[trigger] disjoint_domains(left, right),
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

/// An [`Alt`] parser is disjoint from another parser if both branches are.
pub broadcast proof fn lemma_disjoint_alt_left<
    S1: SpecParser,
    S2: SpecParser<PVal = S1::PVal>,
    S3: SpecParser<PVal = S1::PVal>,
>(alt: Alt<S1, S2>, other: S3)
    requires
        disjoint_domains(alt.0, other),
        disjoint_domains(alt.1, other),
    ensures
        #[trigger] disjoint_domains(alt, other),
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

/// An [`Optional<A, B>`] parser is disjoint from another parser if both `A` and `B` are.
pub broadcast proof fn lemma_disjoint_optional_left<A: SpecParser, B: SpecParser, P: SpecParser>(
    optional: Optional<A, B>,
    p: P,
)
    requires
        disjoint_domains(optional.0, p),
        disjoint_domains(optional.1, p),
    ensures
        #[trigger] disjoint_domains(optional, p),
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

/// A [`Repeat<A, B>`] parser is disjoint from another parser if both `A` and `B` are.
pub broadcast proof fn lemma_disjoint_repeat_left<A: SpecParser, B: SpecParser, P: SpecParser>(
    repeat: Repeat<A, B>,
    p: P,
)
    requires
        disjoint_domains(repeat.0, p),
        disjoint_domains(repeat.1, p),
    ensures
        #[trigger] disjoint_domains(repeat, p),
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

/// [`Eof`] is disjoint from a productive parser.
pub broadcast proof fn lemma_disjoint_eof_left<P: Productive>(eof: Eof, p: P)
    requires
        p.productive_inv(),
        p.safe_inv(),
    ensures
        #[trigger] disjoint_domains(eof, p),
{
    lemma_disjoint_eof(p, eof);
    lemma_disjoint_symmetric(p, eof);
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

/// Naming adaptation does not change a parser's accepted byte domain.
pub broadcast proof fn lemma_disjoint_named_left<Inner: SpecParser, Other: SpecParser>(
    named: Named<Inner>,
    other: Other,
)
    requires
        disjoint_domains(named.1, other),
    ensures
        #[trigger] disjoint_domains(named, other),
{
    reveal(disjoint_domains);
}

/// Naming adaptation does not change a parser's accepted byte domain.
pub broadcast proof fn lemma_disjoint_named_right<Other: SpecParser, Inner: SpecParser>(
    other: Other,
    named: Named<Inner>,
)
    requires
        disjoint_domains(other, named.1),
    ensures
        #[trigger] disjoint_domains(other, named),
{
    reveal(disjoint_domains);
}

/// Compatibility helper for two borrowing adapters.
///
/// This fact is kept directly callable but is not broadcast; the directional `Ref` rules derive
/// it without adding another competing trigger path.
pub proof fn lemma_disjoint_refs<Left: SpecParser, Right: SpecParser>(
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

/// Semantic leaf facts that do not recursively decompose parser syntax.
pub broadcast group disjoint_leaf_lemmas {
    lemma_disjoint_void_left,
    lemma_disjoint_void_right,
    lemma_disjoint_const,
    lemma_disjoint_prefix_tagged,
    lemma_disjoint_refined,
    lemma_disjoint_const_refined,
    lemma_disjoint_cond,
}

/// Domain-preserving or domain-narrowing wrappers on the left of `disjoint_domains`.
pub broadcast group disjoint_left_wrapper_lemmas {
    lemma_disjoint_refined_left,
    lemma_disjoint_mapped_left,
    lemma_disjoint_bimap_left,
    lemma_disjoint_ref_left,
    lemma_disjoint_named_left,
}

/// Domain-preserving or domain-narrowing wrappers on the right of `disjoint_domains`.
pub broadcast group disjoint_right_wrapper_lemmas {
    lemma_disjoint_refined_right,
    lemma_disjoint_mapped,
    lemma_disjoint_bimap,
    lemma_disjoint_ref_right,
    lemma_disjoint_named_right,
}

/// Syntax-directed decomposition of a right-hand continuation.
pub broadcast group disjoint_right_continuation_lemmas {
    lemma_disjoint_tuple,
    lemma_disjoint_bind,
    lemma_disjoint_implicit,
    lemma_disjoint_and_then,
    lemma_disjoint_preceded,
    lemma_disjoint_terminated,
    lemma_disjoint_choice,
    lemma_disjoint_alt,
    lemma_disjoint_optional,
    lemma_disjoint_repeat,
}

/// Reverse-orientation decomposition, available explicitly when a format is left-associated.
pub broadcast group disjoint_left_composite_lemmas {
    lemma_disjoint_tuple_left,
    lemma_disjoint_bind_left,
    lemma_disjoint_implicit_left,
    lemma_disjoint_and_then_left,
    lemma_disjoint_preceded_left,
    lemma_disjoint_terminated_left,
    lemma_disjoint_choice_left,
    lemma_disjoint_alt_left,
    lemma_disjoint_optional_left,
    lemma_disjoint_repeat_left,
}

/// Boundary rules with productivity/safety side conditions.
pub broadcast group disjoint_boundary_lemmas {
    lemma_disjoint_eof,
    lemma_disjoint_eof_left,
    lemma_disjoint_option_end,
    lemma_disjoint_repeat_till_end,
}

/// Canonical automation for right-associated formats.
///
/// Every recursive rule reduces a constructor visible in the trigger. This includes the
/// right-oriented `OptionalEnd` and `RepeatTillEnd` rules: although they expose productivity and
/// safety side conditions, they still strictly peel the triggered continuation. Reverse-oriented
/// rules remain opt-in so that automation cannot oscillate between equivalent orientations.
pub broadcast group disjointness_lemmas {
    lemma_disjoint_void_left,
    lemma_disjoint_void_right,
    lemma_disjoint_choice,
    lemma_disjoint_choices,
    lemma_disjoint_alt,
    lemma_disjoint_const,
    lemma_disjoint_prefix_tagged,
    lemma_disjoint_refined,
    lemma_disjoint_refined_left,
    lemma_disjoint_refined_right,
    lemma_disjoint_const_refined,
    lemma_disjoint_cond,
    lemma_disjoint_tuple,
    lemma_disjoint_bind,
    lemma_disjoint_implicit,
    lemma_disjoint_and_then,
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
    lemma_disjoint_named_left,
    lemma_disjoint_named_right,
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

#[cfg(verus_only)]
proof fn test_directional_disjointness_normalization() {
    broadcast use disjointness_lemmas;

    let first = Const(U8, 1u8);
    let second = Const(U8, 2u8);
    let third = Const(U8, 3u8);

    let tuple = Pair(second, U8);
    assert(disjoint_domains(first, tuple));

    let dependent = Bind(second, |_tag: u8| U8);
    assert(disjoint_domains(first, dependent));

    let named = Named("second", Ref(Refined(second, |_value: u8| true)));
    assert(disjoint_domains(first, named));

    let alternatives = Choice(second, third);
    assert(disjoint_domains(first, alternatives));

    broadcast use disjoint_left_composite_lemmas;

    assert(disjoint_domains(alternatives, first));
}

} // verus!
