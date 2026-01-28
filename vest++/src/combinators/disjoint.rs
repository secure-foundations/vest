use super::choice::Choice;
use super::mapped::spec::Mapper;
use super::mapped::Mapped;
use super::opt::Optional;
use super::preceded::Preceded;
use super::refined::{Refined, Tag};
use super::tail::Eof;
use super::terminated::Terminated;
use super::Repeat;
use crate::core::spec::{disjoint, GoodParser, SpecParser};
use crate::core::types::SpecPred;
use vstd::prelude::*;

verus! {

/// Two [`Tag`] parsers are disjoint if they have the same inner parser but different tag values.
pub broadcast proof fn lemma_disjoint_tag<Inner: SpecParser>(
    tag1: Tag<Inner, Inner::PVal>,
    tag2: Tag<Inner, Inner::PVal>,
)
    requires
        tag1.inner == tag2.inner,
        tag1.tag != tag2.tag,
    ensures
        #[trigger] disjoint(tag1, tag2),
{
}

/// Two [`Refined`] parsers are disjoint if they have the same inner parser
/// and their predicates are mutually exclusive.
pub broadcast proof fn lemma_disjoint_refined<
    Inner: SpecParser,
    P1: SpecPred<Inner::PVal>,
    P2: SpecPred<Inner::PVal>,
>(r1: Refined<Inner, P1>, r2: Refined<Inner, P2>)
    requires
        r1.inner == r2.inner,
        forall|v: Inner::PVal| r1.pred.apply(v) ==> !r2.pred.apply(v),
    ensures
        #[trigger] disjoint(r1, r2),
{
}

/// A tuple parser is disjoint from another parser if its first
/// parser is disjoint from the other parser.
pub broadcast proof fn lemma_disjoint_tuple<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    t: U,
    t1: (U1, V1),
)
    requires
        disjoint(t, t1.0),
    ensures
        #[trigger] disjoint(t, t1),
{
}

/// A [`Preceded`] parser is disjoint from another parser if its first
/// parser is disjoint from the other parser.
pub broadcast proof fn lemma_disjoint_preceded<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    p: U,
    p1: Preceded<U1, V1>,
)
    requires
        disjoint(p, p1.0),
    ensures
        #[trigger] disjoint(p, p1),
{
}

/// A [`Terminated`] parser is disjoint from another parser if its first
/// parser is disjoint from the other parser.
pub broadcast proof fn lemma_disjoint_terminated<U: SpecParser, U1: SpecParser, V1: SpecParser>(
    p: U,
    p1: Terminated<U1, V1>,
)
    requires
        disjoint(p, p1.0),
    ensures
        #[trigger] disjoint(p, p1),
{
}

/// A [`Mapped`] parser is disjoint from another parser if its inner parser is disjoint from it.
pub broadcast proof fn lemma_disjoint_mapped<
    P: SpecParser,
    Inner1: SpecParser,
    M1: Mapper<In = Inner1::PVal>,
>(p: P, m: Mapped<Inner1, M1>)
    requires
        disjoint(p, m.inner),
    ensures
        #[trigger] disjoint(p, m),
{
}

/// A [`Choice`] parser is disjoint from another parser if both branches are disjoint from it.
pub broadcast proof fn lemma_disjoint_choice<S1: SpecParser, S2: SpecParser, S3: SpecParser>(
    choice: Choice<S1, S2>,
    other: S3,
)
    requires
        disjoint(choice.0, other),
        disjoint(choice.1, other),
    ensures
        #[trigger] disjoint(choice, other),
{
}

/// A [`Optional`] parser (which is `(Opt<A>, B)`) is disjoint from another parser if both `A` and `B` are disjoint from it.
pub broadcast proof fn lemma_disjoint_optional<P: SpecParser, A: SpecParser, B: SpecParser>(
    p: P,
    optional: Optional<A, B>,
)
    requires
        disjoint(p, optional.0),
        disjoint(p, optional.1),
    ensures
        #[trigger] disjoint(p, optional),
{
    assert forall|input: Seq<u8>| #[trigger] input.skip(0) == input by {}
}

/// A [`Repeat`] parser (which is `(Star<A>, B)`) is disjoint from another parser if both `A` and `B` are disjoint from it.
pub broadcast proof fn lemma_disjoint_repeat<P: SpecParser, A: SpecParser, B: SpecParser>(
    p: P,
    repeat: Repeat<A, B>,
)
    requires
        disjoint(p, repeat.0),
        disjoint(p, repeat.1),
    ensures
        #[trigger] disjoint(p, repeat),
{
    assert forall|input: Seq<u8>| #[trigger] input.skip(0) == input by {}
}

/// An [`Eof`] parser is disjoint from another parser if the other parser is productive.
pub broadcast proof fn lemma_disjoint_eof<P: GoodParser>(p: P, eof: Eof)
    requires
        p.spec_parse(seq![]) is None,
    ensures
        #[trigger] disjoint(p, eof),
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
