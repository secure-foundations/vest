//! Broadcast lemmas establishing [`disjoint_domains`](crate::core::spec::disjoint_domains)
//! for common combinator compositions.
use super::choice::Choice;
use super::cond::Cond;
use super::mapped::spec::SpecMapper;
use super::mapped::Mapped;
use super::opt::Optional;
use super::preceded::Preceded;
use super::refined::{Refined, Tag};
use super::tail::Eof;
use super::terminated::Terminated;
use super::tuple::Pair;
use super::Repeat;
use crate::core::spec::SpecPred;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

/// Two [`Tag`] parsers with the same inner parser but different tag values are disjoint.
pub broadcast proof fn lemma_disjoint_tag<Inner: SpecParser>(
    tag1: Tag<Inner, Inner::PVal>,
    tag2: Tag<Inner, Inner::PVal>,
)
    requires
        tag1.inner == tag2.inner,
        tag1.tag != tag2.tag,
    ensures
        #[trigger] disjoint_domains(tag1, tag2),
{
}

/// Two [`Refined`] parsers with the same inner parser and mutually exclusive predicates are disjoint.
pub broadcast proof fn lemma_disjoint_refined<
    Inner: SpecParser,
    P1: SpecPred<Inner::PVal>,
    P2: SpecPred<Inner::PVal>,
>(r1: Refined<Inner, P1>, r2: Refined<Inner, P2>)
    requires
        r1.inner == r2.inner,
        forall|v: Inner::PVal| r1.pred.apply(v) ==> !r2.pred.apply(v),
    ensures
        #[trigger] disjoint_domains(r1, r2),
{
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
}

/// A [`Preceded`] parser is disjoint from another parser if its prefix is.
pub broadcast proof fn lemma_disjoint_preceded<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    p: U,
    p1: Preceded<U1, V1>,
)
    requires
        disjoint_domains(p, p1.0),
    ensures
        #[trigger] disjoint_domains(p, p1),
{
}

/// A [`Terminated`] parser is disjoint from another parser if its prefix is.
pub broadcast proof fn lemma_disjoint_terminated<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    p: U,
    p1: Terminated<U1, V1>,
)
    requires
        disjoint_domains(p, p1.0),
    ensures
        #[trigger] disjoint_domains(p, p1),
{
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
}

/// A [`Choice`] parser is disjoint from another parser if both branches are.
pub broadcast proof fn lemma_disjoint_choice<S1: SpecParser, S2: SpecParser, S3: SpecParser>(
    choice: Choice<S1, S2>,
    other: S3,
)
    requires
        disjoint_domains(choice.0, other),
        disjoint_domains(choice.1, other),
    ensures
        #[trigger] disjoint_domains(choice, other),
{
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
    broadcast use vstd::seq_lib::lemma_seq_skip_nothing;

}

/// A productive parser (one that fails on empty input) is disjoint from [`Eof`].
pub broadcast proof fn lemma_disjoint_eof<P: SoundParser>(p: P, eof: Eof)
    requires
        p.spec_parse(seq![]) is None,
    ensures
        #[trigger] disjoint_domains(p, eof),
{
    assert forall|input: Seq<u8>|
        #![auto]
        p.spec_parse(input) is Some && eof.spec_parse(input) is Some implies false by {
        if eof.spec_parse(input) is Some {
            assert(input.len() == 0);
            assert(input == Seq::<u8>::empty());
        }
    }
}

} // verus!
