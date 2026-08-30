//! Congruence lemmas for parser, serializer, and preparation specifications.
use crate::combinators::bits::Bits;
use crate::combinators::bytes::{AndThen, ExactLen, Fixed, Varied};
use crate::combinators::mapped::spec::{BiMap, BiMapper, FnSpecMapper, SpecMap};
use crate::combinators::named::Named;
use crate::combinators::reference::Ref;
use crate::combinators::tail::{Eof, RepeatTillEnd, Tail};
use crate::combinators::AsLen;
use crate::combinators::Optional;
use crate::combinators::OptionalEnd;
use crate::combinators::{
    Alt, Array, Bind, Choice, Cond, Const, Mapped, Opt, Pair, Preceded, PrefixTagged, Refined,
    Repeat, RepeatN, Star, SuffixTagged, Sum, Terminated,
};
use crate::core::exec::fns::FnParser;
use crate::core::exec::parser::PResult;
use crate::core::spec::{
    BytesCombinator, Consistency, SafeParser, SpecByteLen, SpecParser, SpecPred, SpecSerializer,
    SpecSerializerDps,
};
use vstd::prelude::*;

verus! {

/// Pointwise equality of parser denotations. The format types may differ, but their parsed value
/// types must agree.
#[verifier::opaque]
pub open spec fn parser_congruent<A, B>(a: A, b: B) -> bool where
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
 {
    forall|input: Seq<u8>| a.spec_parse(input) == b.spec_parse(input)
}

/// Equality of the two semantic components used by executable preparation.
#[verifier::opaque]
pub open spec fn prepare_congruent<A, B>(a: A, b: B) -> bool where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
 {
    &&& forall|v: A::Val| a.consistent(v) <==> b.consistent(v)
    &&& forall|v: A::Val| a.byte_len(v) == b.byte_len(v)
}

/// Equality of the full semantic interface used by executable serialization.
#[verifier::opaque]
pub open spec fn serializer_congruent<A, B>(a: A, b: B) -> bool where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
 {
    &&& prepare_congruent(a, b)
    &&& forall|v: A::Val| a.spec_serialize(v) == b.spec_serialize(v)
}

pub broadcast proof fn lemma_parser_congruent_apply<A, B>(a: A, b: B, input: Seq<u8>) where
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,

    requires
        parser_congruent(a, b),
    ensures
        #[trigger] a.spec_parse(input) == #[trigger] b.spec_parse(input),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_parser_congruent_intro<A, B>(a: A, b: B) where
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,

    requires
        forall|input: Seq<u8>| #[trigger] a.spec_parse(input) == b.spec_parse(input),
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
}

/// Connects an executable parser callback, through the Rust reference adapter, directly to its
/// ghost parser. This packages the otherwise repetitive pointwise `spec_parse` proof.
pub broadcast proof fn lemma_ref_fn_parser_congruence<I, O, Spec, Exec>(
    parser: &FnParser<I, O, Spec, Exec>,
) where I: View<V = Seq<u8>>, O: DeepView, Spec: SpecParser<PVal = O::V>, Exec: Fn(&I) -> PResult<O>
    ensures
        #[trigger] parser_congruent(parser, parser.spec_fn@),
{
    reveal(parser_congruent);
    assert forall|input: Seq<u8>| #[trigger]
        (&parser).spec_parse(input) == parser.spec_fn@.spec_parse(input) by {
        crate::core::exec::fns::lemma_ref_fn_parser_spec_parse(parser, input);
    }
}

pub broadcast proof fn lemma_prepare_congruent_intro<A, B>(a: A, b: B) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        forall|v: A::Val| #[trigger] a.consistent(v) <==> b.consistent(v),
        forall|v: A::Val| #[trigger] a.byte_len(v) == b.byte_len(v),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_serializer_congruent_intro<A, B>(a: A, b: B) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        prepare_congruent(a, b),
        forall|v: A::Val| #[trigger] a.spec_serialize(v) == b.spec_serialize(v),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
}

pub broadcast proof fn lemma_prepare_congruent_consistent<A, B>(a: A, b: B, v: A::Val) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a, b),
    ensures
        #[trigger] a.consistent(v) <==> #[trigger] b.consistent(v),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_prepare_congruent_byte_len<A, B>(a: A, b: B, v: A::Val) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a, b),
    ensures
        #[trigger] a.byte_len(v) == #[trigger] b.byte_len(v),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_serializer_congruent_prepare<A, B>(a: A, b: B) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a, b),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(serializer_congruent);
}

pub broadcast proof fn lemma_serializer_congruent_serialize<A, B>(a: A, b: B, v: A::Val) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a, b),
    ensures
        #[trigger] a.spec_serialize(v) == #[trigger] b.spec_serialize(v),
{
    reveal(serializer_congruent);
}

pub broadcast proof fn lemma_parser_congruent_reflexive<A: SpecParser>(a: A)
    ensures
        #[trigger] parser_congruent(a, a),
{
    reveal(parser_congruent);
}

// Symmetry and transitivity stay explicit: broadcasting them would compute an unrestricted
// congruence closure (including symmetric ping-pong and quadratic transitive instantiations).
pub proof fn lemma_parser_congruent_symmetric<A, B>(a: A, b: B) where
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,

    requires
        parser_congruent(a, b),
    ensures
        parser_congruent(b, a),
{
    reveal(parser_congruent);
}

pub proof fn lemma_parser_congruent_transitive<A, B, C>(a: A, b: B, c: C) where
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    C: SpecParser<PVal = A::PVal>,

    requires
        parser_congruent(a, b),
        parser_congruent(b, c),
    ensures
        parser_congruent(a, c),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_prepare_congruent_reflexive<A>(a: A) where
    A: Consistency + SpecByteLen<T = A::Val>,

    ensures
        #[trigger] prepare_congruent(a, a),
{
    reveal(prepare_congruent);
}

pub proof fn lemma_prepare_congruent_symmetric<A, B>(a: A, b: B) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a, b),
    ensures
        prepare_congruent(b, a),
{
    reveal(prepare_congruent);
}

pub proof fn lemma_prepare_congruent_transitive<A, B, C>(a: A, b: B, c: C) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
    C: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a, b),
        prepare_congruent(b, c),
    ensures
        prepare_congruent(a, c),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_serializer_congruent_reflexive<A>(a: A) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    ensures
        #[trigger] serializer_congruent(a, a),
{
    reveal(serializer_congruent);
    lemma_prepare_congruent_reflexive(a);
}

pub proof fn lemma_serializer_congruent_symmetric<A, B>(a: A, b: B) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a, b),
    ensures
        serializer_congruent(b, a),
{
    reveal(serializer_congruent);
    lemma_prepare_congruent_symmetric(a, b);
}

pub proof fn lemma_serializer_congruent_transitive<A, B, C>(a: A, b: B, c: C) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    C: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a, b),
        serializer_congruent(b, c),
    ensures
        serializer_congruent(a, c),
{
    reveal(serializer_congruent);
    lemma_prepare_congruent_transitive(a, b, c);
}

// ----------------------------------------------------
// ExactLen
// ----------------------------------------------------
pub proof fn lemma_exact_len_spec_parse_congruence<
    Inner: SpecParser,
    Inner2: SpecParser<PVal = Inner::PVal>,
    Len: AsLen,
>(len: Len, inner: Inner, inner2: Inner2)
    requires
        forall|x: Seq<u8>| #[trigger] inner.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            ExactLen(len, inner).spec_parse(x) == ExactLen(len, inner2).spec_parse(x),
{
}

// ----------------------------------------------------
// AndThen
// ----------------------------------------------------
pub proof fn lemma_and_then_spec_parse_congruence<
    Tail1: SpecParser<PVal = Seq<u8>>,
    Tail2: SpecParser<PVal = Seq<u8>>,
    Then1: SpecParser,
    Then2: SpecParser<PVal = Then1::PVal>,
>(tail1: Tail1, tail2: Tail2, then1: Then1, then2: Then2)
    requires
        forall|x: Seq<u8>| #[trigger] tail1.spec_parse(x) == tail2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] then1.spec_parse(x) == then2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            AndThen(tail1, then1).spec_parse(x) == AndThen(tail2, then2).spec_parse(x),
{
}

// ----------------------------------------------------
// Mapped
// ----------------------------------------------------
pub proof fn lemma_mapped_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
    M1: crate::combinators::mapped::spec::SpecMapper<In = Inner1::PVal>,
    M2: crate::combinators::mapped::spec::SpecMapper<In = Inner2::PVal, Out = M1::Out>,
>(inner1: Inner1, inner2: Inner2, mapper1: M1, mapper2: M2)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
        forall|v: Inner1::PVal| #[trigger] mapper1.spec_map(v) == mapper2.spec_map(v),
    ensures
        forall|x: Seq<u8>| #[trigger]
            (Mapped { inner: inner1, mapper: mapper1 }).spec_parse(x) == (Mapped {
                inner: inner2,
                mapper: mapper2,
            }).spec_parse(x),
{
}

// ----------------------------------------------------
// Refined
// ----------------------------------------------------
pub proof fn lemma_refined_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
    Pred: SpecPred<Inner1::PVal>,
>(inner1: Inner1, inner2: Inner2, pred: Pred)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Refined(inner1, pred).spec_parse(x) == Refined(inner2, pred).spec_parse(x),
{
}

// ----------------------------------------------------
// Const
// ----------------------------------------------------
pub proof fn lemma_const_spec_parse_congruence<
    Inner1: SpecParser<PVal = T>,
    Inner2: SpecParser<PVal = T>,
    T,
>(inner1: Inner1, inner2: Inner2, val: T)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Const(inner1, val).spec_parse(x) == Const(inner2, val).spec_parse(x),
{
}

// ----------------------------------------------------
// Cond
// ----------------------------------------------------
pub proof fn lemma_cond_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(cond: bool, inner1: Inner1, inner2: Inner2)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Cond(cond, inner1).spec_parse(x) == Cond(cond, inner2).spec_parse(x),
{
}

// ----------------------------------------------------
// Choice
// ----------------------------------------------------
pub proof fn lemma_choice_spec_parse_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Choice(a1, b1).spec_parse(x) == Choice(a2, b2).spec_parse(x),
{
}

// ----------------------------------------------------
// Alt
// ----------------------------------------------------
pub proof fn lemma_alt_spec_parse_congruence<
    const NONDETERMINISTIC: bool,
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser<PVal = A1::PVal>,
    B2: SpecParser<PVal = A1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Alt::<A1, B1, NONDETERMINISTIC>(a1, b1).spec_parse(x) == Alt::<
                A2,
                B2,
                NONDETERMINISTIC,
            >(a2, b2).spec_parse(x),
{
}

// ----------------------------------------------------
// Sum
// ----------------------------------------------------
pub proof fn lemma_sum_spec_parse_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Sum::<A1, B1>::Inl(a1).spec_parse(x) == Sum::<A2, B2>::Inl(a2).spec_parse(x),
        forall|x: Seq<u8>| #[trigger]
            Sum::<A1, B1>::Inr(b1).spec_parse(x) == Sum::<A2, B2>::Inr(b2).spec_parse(x),
{
}

// ----------------------------------------------------
// Opt
// ----------------------------------------------------
pub proof fn lemma_opt_spec_parse_congruence<A: SpecParser, B: SpecParser<PVal = A::PVal>>(
    a: A,
    b: B,
)
    requires
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Opt(a).spec_parse(x) == Opt(b).spec_parse(x),
{
}

// ----------------------------------------------------
// Optional
// ----------------------------------------------------
pub proof fn lemma_optional_spec_parse_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Optional(a1, b1).spec_parse(x) == Optional(a2, b2).spec_parse(x),
{
    lemma_opt_spec_parse_congruence(a1, a2);
    lemma_pair_spec_parse_congruence(Opt(a1), Opt(a2), b1, b2);
}

// ----------------------------------------------------
// OptionalEnd
// ----------------------------------------------------
pub proof fn lemma_optional_end_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(inner1: Inner1, inner2: Inner2)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            OptionalEnd(inner1).spec_parse(x) == OptionalEnd(inner2).spec_parse(x),
{
    lemma_optional_spec_parse_congruence(inner1, inner2, Eof, Eof);
}

// ----------------------------------------------------
// Preceded
// ----------------------------------------------------
pub proof fn lemma_preceded_spec_parse_congruence<
    const CHECK: bool,
    A1: SpecParser<PVal = AVal>,
    A2: SpecParser<PVal = AVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
    AVal,
>(a1: A1, a2: A2, b1: B1, b2: B2, a_val: AVal)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            (Preceded::<A1, AVal, B1, CHECK> { a: a1, b: b1, a_val }).spec_parse(x) == (Preceded::<
                A2,
                AVal,
                B2,
                CHECK,
            > { a: a2, b: b2, a_val }).spec_parse(x),
{
    lemma_pair_spec_parse_congruence(a1, a2, b1, b2);
}

// ----------------------------------------------------
// Terminated
// ----------------------------------------------------
pub proof fn lemma_terminated_spec_parse_congruence<
    const CHECK: bool,
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser<PVal = BVal>,
    B2: SpecParser<PVal = BVal>,
    BVal,
>(a1: A1, a2: A2, b1: B1, b2: B2, b_val: BVal)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            (Terminated::<A1, B1, BVal, CHECK> { a: a1, b: b1, b_val }).spec_parse(x) == (
            Terminated::<A2, B2, BVal, CHECK> { a: a2, b: b2, b_val }).spec_parse(x),
{
    lemma_pair_spec_parse_congruence(a1, a2, b1, b2);
}

// ----------------------------------------------------
// Pair
// ----------------------------------------------------
pub proof fn lemma_pair_spec_parse_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|x: Seq<u8>| #[trigger] b1.spec_parse(x) == b2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Pair(a1, b1).spec_parse(x) == Pair(a2, b2).spec_parse(x),
{
}

// ----------------------------------------------------
// Bind
// ----------------------------------------------------
pub proof fn lemma_bind_spec_parse_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecMap<Input = A1::PVal>,
    B2: SpecMap<Input = A2::PVal>,
    OutVal,
>(a1: A1, a2: A2, b1: B1, b2: B2) where
    B1::Output: SpecParser<PVal = OutVal>,
    B2::Output: SpecParser<PVal = OutVal>,

    requires
        forall|x: Seq<u8>| #[trigger] a1.spec_parse(x) == a2.spec_parse(x),
        forall|key: A1::PVal, x: Seq<u8>| #[trigger]
            b1.spec_map(key).spec_parse(x) == b2.spec_map(key).spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Bind(a1, b1).spec_parse(x) == Bind(a2, b2).spec_parse(x),
{
}

// ----------------------------------------------------
// Ref
// ----------------------------------------------------
pub proof fn lemma_ref_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(inner1: Inner1, inner2: Inner2)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Ref(inner1).spec_parse(x) == Ref(inner2).spec_parse(x),
{
}

// ----------------------------------------------------
// Named
// ----------------------------------------------------
pub proof fn lemma_named_spec_parse_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(name: &'static str, inner1: Inner1, inner2: Inner2)
    requires
        forall|x: Seq<u8>| #[trigger] inner1.spec_parse(x) == inner2.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            Named(name, inner1).spec_parse(x) == Named(name, inner2).spec_parse(x),
{
}

// ----------------------------------------------------
// Star / Repeat / RepeatTillEnd
// ----------------------------------------------------
pub proof fn lemma_star_parse_rec_congruence<A: SpecParser, B: SpecParser<PVal = A::PVal>>(
    a: A,
    b: B,
    ibuf: Seq<u8>,
)
    requires
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
    ensures
        Star(a).parse_rec(ibuf) == Star(b).parse_rec(ibuf),
    decreases ibuf.len(),
{
    if let Some((n, _v)) = a.spec_parse(ibuf) {
        if 0 < n <= ibuf.len() {
            lemma_star_parse_rec_congruence(a, b, ibuf.skip(n));
        }
    }
}

pub proof fn lemma_star_spec_parse_congruence<A: SpecParser, B: SpecParser<PVal = A::PVal>>(
    a: A,
    b: B,
)
    requires
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Star(a).spec_parse(x) == Star(b).spec_parse(x),
{
    reveal(<Star::<_> as SpecParser>::spec_parse);
    assert forall|x: Seq<u8>| #[trigger] Star(a).spec_parse(x) == Star(b).spec_parse(x) by {
        lemma_star_parse_rec_congruence(a, b, x);
    }
}

pub proof fn lemma_repeat_spec_parse_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    T: SpecParser,
>(a: A, b: B, t: T)
    requires
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger] Repeat(a, t).spec_parse(x) == Repeat(b, t).spec_parse(x),
{
    lemma_star_spec_parse_congruence(a, b);
    lemma_pair_spec_parse_congruence(Star(a), Star(b), t, t);
}

pub proof fn lemma_repeat_till_end_spec_parse_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
>(a: A, b: B)
    requires
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
    ensures
        forall|x: Seq<u8>| #[trigger]
            RepeatTillEnd(a).spec_parse(x) == RepeatTillEnd(b).spec_parse(x),
{
    lemma_repeat_spec_parse_congruence(a, b, Eof);
}

// ----------------------------------------------------
// RepeatN
// ----------------------------------------------------
pub proof fn lemma_repeat_n_parse_n_rec_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    N: AsLen,
>(a: &RepeatN<A, N>, b: &RepeatN<B, N>, count: nat, ibuf: Seq<u8>)
    requires
        forall|x: Seq<u8>| #[trigger] a.1.spec_parse(x) == b.1.spec_parse(x),
    ensures
        a.parse_n_rec(count, ibuf) == b.parse_n_rec(count, ibuf),
    decreases count,
{
    if count == 0 {
    } else {
        assert(a.1.spec_parse(ibuf) == b.1.spec_parse(ibuf));
        if let Some((n0, _)) = a.1.spec_parse(ibuf) {
            lemma_repeat_n_parse_n_rec_congruence(a, b, (count - 1) as nat, ibuf.skip(n0));
        }
    }
}

pub proof fn lemma_repeat_n_spec_parse_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    N: AsLen,
>(a: RepeatN<A, N>, b: RepeatN<B, N>)
    requires
        forall|x: Seq<u8>| #[trigger] a.1.spec_parse(x) == b.1.spec_parse(x),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x),
{
    assert forall|x: Seq<u8>| #[trigger] a.spec_parse(x) == b.spec_parse(x) by {
        lemma_repeat_n_parse_n_rec_congruence(&a, &b, a.0.as_nat(), x);
    }
}

// ====================================================
// Named parser-congruence lifting API
// ====================================================
pub broadcast proof fn lemma_exact_len_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
    Len: AsLen,
>(len: Len, inner1: Inner1, inner2: Inner2)
    requires
        parser_congruent(inner1, inner2),
    ensures
        #[trigger] parser_congruent(ExactLen(len, inner1), ExactLen(len, inner2)),
{
    reveal(parser_congruent);
    lemma_exact_len_spec_parse_congruence(len, inner1, inner2);
}

pub broadcast proof fn lemma_pair_parser_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        parser_congruent(a1, a2),
        parser_congruent(b1, b2),
    ensures
        #[trigger] parser_congruent(Pair(a1, b1), Pair(a2, b2)),
{
    reveal(parser_congruent);
    lemma_pair_spec_parse_congruence(a1, a2, b1, b2);
}

pub broadcast proof fn lemma_ref_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(inner1: Inner1, inner2: Inner2)
    requires
        parser_congruent(inner1, inner2),
    ensures
        #[trigger] parser_congruent(Ref(inner1), Ref(inner2)),
{
    reveal(parser_congruent);
    lemma_ref_spec_parse_congruence(inner1, inner2);
}

pub broadcast proof fn lemma_named_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(name1: &'static str, name2: &'static str, inner1: Inner1, inner2: Inner2)
    requires
        parser_congruent(inner1, inner2),
    ensures
        #[trigger] parser_congruent(Named(name1, inner1), Named(name2, inner2)),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_star_parser_congruence<A: SpecParser, B: SpecParser<PVal = A::PVal>>(
    a: A,
    b: B,
)
    requires
        parser_congruent(a, b),
    ensures
        #[trigger] parser_congruent(Star(a), Star(b)),
{
    reveal(parser_congruent);
    lemma_star_spec_parse_congruence(a, b);
}

pub broadcast proof fn lemma_repeat_parser_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    T1: SpecParser,
    T2: SpecParser<PVal = T1::PVal>,
>(a: A, b: B, t1: T1, t2: T2)
    requires
        parser_congruent(a, b),
        parser_congruent(t1, t2),
    ensures
        #[trigger] parser_congruent(Repeat(a, t1), Repeat(b, t2)),
{
    reveal(parser_congruent);
    lemma_star_spec_parse_congruence(a, b);
    lemma_pair_spec_parse_congruence(Star(a), Star(b), t1, t2);
}

pub broadcast proof fn lemma_repeat_till_end_parser_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
>(a: A, b: B)
    requires
        parser_congruent(a, b),
    ensures
        #[trigger] parser_congruent(RepeatTillEnd(a), RepeatTillEnd(b)),
{
    reveal(parser_congruent);
    lemma_repeat_till_end_spec_parse_congruence(a, b);
}

pub broadcast proof fn lemma_repeat_n_parser_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    N: AsLen,
>(a: RepeatN<A, N>, b: RepeatN<B, N>)
    requires
        parser_congruent(a.1, b.1),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    lemma_repeat_n_spec_parse_congruence(a, b);
}

pub broadcast proof fn lemma_array_parser_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
    const N: usize,
>(a: A, b: B)
    requires
        parser_congruent(a, b),
    ensures
        #[trigger] parser_congruent(Array::<N, A>(a), Array::<N, B>(b)),
{
    reveal(parser_congruent);
    lemma_repeat_n_spec_parse_congruence(RepeatN(N, a), RepeatN(N, b));
}

pub broadcast proof fn lemma_and_then_parser_congruence<
    Tail1: SpecParser<PVal = Seq<u8>>,
    Tail2: SpecParser<PVal = Seq<u8>>,
    Then1: SpecParser,
    Then2: SpecParser<PVal = Then1::PVal>,
>(tail1: Tail1, tail2: Tail2, then1: Then1, then2: Then2)
    requires
        parser_congruent(tail1, tail2),
        parser_congruent(then1, then2),
    ensures
        #[trigger] parser_congruent(AndThen(tail1, then1), AndThen(tail2, then2)),
{
    reveal(parser_congruent);
    lemma_and_then_spec_parse_congruence(tail1, tail2, then1, then2);
}

pub broadcast proof fn lemma_mapped_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
    M1: crate::combinators::mapped::spec::SpecMapper<In = Inner1::PVal>,
    M2: crate::combinators::mapped::spec::SpecMapper<In = Inner2::PVal, Out = M1::Out>,
>(inner1: Inner1, inner2: Inner2, mapper1: M1, mapper2: M2)
    requires
        parser_congruent(inner1, inner2),
        forall|v: Inner1::PVal| #[trigger] mapper1.spec_map(v) == mapper2.spec_map(v),
    ensures
        #[trigger] parser_congruent(
            Mapped { inner: inner1, mapper: mapper1 },
            Mapped { inner: inner2, mapper: mapper2 },
        ),
{
    reveal(parser_congruent);
    lemma_mapped_spec_parse_congruence(inner1, inner2, mapper1, mapper2);
}

pub broadcast proof fn lemma_refined_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
    P1: SpecPred<Inner1::PVal>,
    P2: SpecPred<Inner1::PVal>,
>(a: Refined<Inner1, P1>, b: Refined<Inner2, P2>)
    requires
        parser_congruent(a.0, b.0),
        forall|v: Inner1::PVal| #[trigger] a.1.apply(v) <==> b.1.apply(v),
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_const_parser_congruence<
    Inner1: SpecParser<PVal = T>,
    Inner2: SpecParser<PVal = T>,
    T,
>(a: Const<Inner1, T>, b: Const<Inner2, T>)
    requires
        parser_congruent(a.0, b.0),
        a.1 == b.1,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_cond_parser_congruence<
    Inner1: SpecParser,
    Inner2: SpecParser<PVal = Inner1::PVal>,
>(a: Cond<Inner1>, b: Cond<Inner2>)
    requires
        a.0 == b.0,
        parser_congruent(a.1, b.1),
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
}

pub broadcast proof fn lemma_choice_parser_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        parser_congruent(a1, a2),
        parser_congruent(b1, b2),
    ensures
        #[trigger] parser_congruent(Choice(a1, b1), Choice(a2, b2)),
{
    reveal(parser_congruent);
    lemma_choice_spec_parse_congruence(a1, a2, b1, b2);
}

pub broadcast proof fn lemma_alt_parser_congruence<
    const NONDETERMINISTIC: bool,
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser<PVal = A1::PVal>,
    B2: SpecParser<PVal = A1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        parser_congruent(a1, a2),
        parser_congruent(b1, b2),
    ensures
        #[trigger] parser_congruent(
            Alt::<A1, B1, NONDETERMINISTIC>(a1, b1),
            Alt::<A2, B2, NONDETERMINISTIC>(a2, b2),
        ),
{
    reveal(parser_congruent);
    lemma_alt_spec_parse_congruence::<NONDETERMINISTIC, _, _, _, _>(a1, a2, b1, b2);
}

pub broadcast proof fn lemma_opt_parser_congruence<A: SpecParser, B: SpecParser<PVal = A::PVal>>(
    a: A,
    b: B,
)
    requires
        parser_congruent(a, b),
    ensures
        #[trigger] parser_congruent(Opt(a), Opt(b)),
{
    reveal(parser_congruent);
    lemma_opt_spec_parse_congruence(a, b);
}

pub broadcast proof fn lemma_optional_parser_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a1: A1, a2: A2, b1: B1, b2: B2)
    requires
        parser_congruent(a1, a2),
        parser_congruent(b1, b2),
    ensures
        #[trigger] parser_congruent(Optional(a1, b1), Optional(a2, b2)),
{
    reveal(parser_congruent);
    lemma_optional_spec_parse_congruence(a1, a2, b1, b2);
}

pub broadcast proof fn lemma_optional_end_parser_congruence<
    A: SpecParser,
    B: SpecParser<PVal = A::PVal>,
>(a: A, b: B)
    requires
        parser_congruent(a, b),
    ensures
        #[trigger] parser_congruent(OptionalEnd(a), OptionalEnd(b)),
{
    reveal(parser_congruent);
    lemma_optional_end_spec_parse_congruence(a, b);
}

pub broadcast proof fn lemma_preceded_parser_congruence<
    const CHECK: bool,
    A1: SpecParser<PVal = AVal>,
    A2: SpecParser<PVal = AVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
    AVal,
>(a: Preceded<A1, AVal, B1, CHECK>, b: Preceded<A2, AVal, B2, CHECK>)
    requires
        parser_congruent(a.a, b.a),
        parser_congruent(a.b, b.b),
        a.a_val == b.a_val,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    lemma_preceded_spec_parse_congruence::<CHECK, _, _, _, _, _>(a.a, b.a, a.b, b.b, a.a_val);
}

pub broadcast proof fn lemma_terminated_parser_congruence<
    const CHECK: bool,
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser<PVal = BVal>,
    B2: SpecParser<PVal = BVal>,
    BVal,
>(a: Terminated<A1, B1, BVal, CHECK>, b: Terminated<A2, B2, BVal, CHECK>)
    requires
        parser_congruent(a.a, b.a),
        parser_congruent(a.b, b.b),
        a.b_val == b.b_val,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    lemma_terminated_spec_parse_congruence::<CHECK, _, _, _, _, _>(a.a, b.a, a.b, b.b, a.b_val);
}

pub broadcast proof fn lemma_bind_parser_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecMap<Input = A1::PVal>,
    B2: SpecMap<Input = A2::PVal>,
>(a: Bind<A1, B1>, b: Bind<A2, B2>) where
    B1::Output: SpecParser,
    B2::Output: SpecParser<PVal = <B1::Output as SpecParser>::PVal>,

    requires
        parser_congruent(a.0, b.0),
        forall|key: A1::PVal| #[trigger] parser_congruent(a.1.spec_map(key), b.1.spec_map(key)),
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    broadcast use lemma_parser_congruent_apply;

    lemma_bind_spec_parse_congruence(a.0, b.0, a.1, b.1);
}

pub broadcast proof fn lemma_sum_parser_congruence<
    A1: SpecParser,
    A2: SpecParser<PVal = A1::PVal>,
    B1: SpecParser,
    B2: SpecParser<PVal = B1::PVal>,
>(a: Sum<A1, B1>, b: Sum<A2, B2>)
    requires
        match (a, b) {
            (Sum::Inl(a), Sum::Inl(b)) => parser_congruent(a, b),
            (Sum::Inr(a), Sum::Inr(b)) => parser_congruent(a, b),
            _ => false,
        },
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    match (a, b) {
        (Sum::Inl(a), Sum::Inl(b)) => lemma_sum_spec_parse_congruence(a, b, a, b),
        (Sum::Inr(a), Sum::Inr(b)) => lemma_sum_spec_parse_congruence(a, b, a, b),
        _ => {},
    }
}

// ====================================================
// Preparation / serializer congruence: unary formats
// ====================================================
pub broadcast proof fn lemma_exact_len_prepare_congruence<A, B, L1, L2>(
    a: ExactLen<A, L1>,
    b: ExactLen<B, L2>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
    L1: AsLen,
    L2: AsLen,

    requires
        prepare_congruent(a.1, b.1),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_exact_len_serializer_congruence<A, B, L1, L2>(
    a: ExactLen<A, L1>,
    b: ExactLen<B, L2>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    L1: AsLen,
    L2: AsLen,

    requires
        serializer_congruent(a.1, b.1),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_exact_len_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_refined_prepare_congruence<A, B, P1, P2>(
    a: Refined<A, P1>,
    b: Refined<B, P2>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
    P1: SpecPred<A::Val>,
    P2: SpecPred<A::Val>,

    requires
        prepare_congruent(a.0, b.0),
        forall|v: A::Val| #[trigger] a.1.apply(v) <==> b.1.apply(v),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_refined_serializer_congruence<A, B, P1, P2>(
    a: Refined<A, P1>,
    b: Refined<B, P2>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    P1: SpecPred<A::Val>,
    P2: SpecPred<A::Val>,

    requires
        serializer_congruent(a.0, b.0),
        forall|v: A::Val| #[trigger] a.1.apply(v) <==> b.1.apply(v),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_refined_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_cond_prepare_congruence<A, B>(a: Cond<A>, b: Cond<B>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        a.0 == b.0,
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_cond_serializer_congruence<A, B>(a: Cond<A>, b: Cond<B>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        a.0 == b.0,
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_cond_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_const_prepare_congruence<A, B>(
    a: Const<A, A::Val>,
    b: Const<B, A::Val>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        a.1 == b.1,
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_const_serializer_congruence<A, B>(
    a: Const<A, A::Val>,
    b: Const<B, A::Val>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        a.1 == b.1,
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_const_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_opt_prepare_congruence<A, B>(a: Opt<A>, b: Opt<B>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_opt_serializer_congruence<A, B>(a: Opt<A>, b: Opt<B>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_opt_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_ref_prepare_congruence<A, B>(a: Ref<A>, b: Ref<B>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_ref_serializer_congruence<A, B>(a: Ref<A>, b: Ref<B>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_ref_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_named_prepare_congruence<A, B>(a: Named<A>, b: Named<B>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_named_serializer_congruence<A, B>(a: Named<A>, b: Named<B>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_named_prepare_congruence(a, b);
}

// ====================================================
// Preparation / serializer congruence: compositions
// ====================================================
proof fn lemma_star_byte_len_congruence_rec<A, B>(a: A, b: B, vs: Seq<A::Val>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a, b),
    ensures
        Star(a).byte_len(vs) == Star(b).byte_len(vs),
    decreases vs.len(),
{
    reveal(prepare_congruent);
    reveal(<Star::<_> as SpecByteLen>::byte_len);
    if vs.len() > 0 {
        lemma_star_byte_len_congruence_rec(a, b, vs.drop_last());
    }
}

proof fn lemma_star_serialize_congruence_rec<A, B>(a: A, b: B, vs: Seq<A::Val>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a, b),
    ensures
        Star(a).spec_serialize(vs) == Star(b).spec_serialize(vs),
    decreases vs.len(),
{
    reveal(serializer_congruent);
    reveal(<Star::<_> as SpecSerializer>::spec_serialize);
    if vs.len() > 0 {
        lemma_star_serialize_congruence_rec(a, b, vs.drop_last());
    }
}

pub broadcast proof fn lemma_star_prepare_congruence<A, B>(a: Star<A>, b: Star<B>) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    reveal(<Star::<_> as Consistency>::consistent);
    assert forall|vs: Seq<A::Val>| #[trigger] a.byte_len(vs) == b.byte_len(vs) by {
        lemma_star_byte_len_congruence_rec(a.0, b.0, vs);
    }
}

pub broadcast proof fn lemma_star_serializer_congruence<A, B>(a: Star<A>, b: Star<B>) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_star_prepare_congruence(a, b);
    assert forall|vs: Seq<A::Val>| #[trigger] a.spec_serialize(vs) == b.spec_serialize(vs) by {
        lemma_star_serialize_congruence_rec(a.0, b.0, vs);
    }
}

pub broadcast proof fn lemma_pair_prepare_congruence<A1, A2, B1, B2>(
    a: Pair<A1, B1>,
    b: Pair<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_pair_serializer_congruence<A1, A2, B1, B2>(
    a: Pair<A1, B1>,
    b: Pair<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_pair_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_choice_prepare_congruence<A1, A2, B1, B2>(
    a: Choice<A1, B1>,
    b: Choice<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_choice_serializer_congruence<A1, A2, B1, B2>(
    a: Choice<A1, B1>,
    b: Choice<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_choice_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_optional_prepare_congruence<A1, A2, B1, B2>(
    a: Optional<A1, B1>,
    b: Optional<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_opt_prepare_congruence(Opt(a.0), Opt(b.0));
    lemma_pair_prepare_congruence(Pair(Opt(a.0), a.1), Pair(Opt(b.0), b.1));
}

pub broadcast proof fn lemma_optional_serializer_congruence<A1, A2, B1, B2>(
    a: Optional<A1, B1>,
    b: Optional<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_optional_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_repeat_prepare_congruence<A1, A2, B1, B2>(
    a: Repeat<A1, B1>,
    b: Repeat<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_star_prepare_congruence(Star(a.0), Star(b.0));
    lemma_pair_prepare_congruence(Pair(Star(a.0), a.1), Pair(Star(b.0), b.1));
}

pub broadcast proof fn lemma_repeat_serializer_congruence<A1, A2, B1, B2>(
    a: Repeat<A1, B1>,
    b: Repeat<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_repeat_prepare_congruence(a, b);
    lemma_star_serializer_congruence(Star(a.0), Star(b.0));
}

pub broadcast proof fn lemma_repeat_n_prepare_congruence<A, B, N1, N2>(
    a: RepeatN<A, N1>,
    b: RepeatN<B, N2>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
    N1: AsLen,
    N2: AsLen,

    requires
        prepare_congruent(a.1, b.1),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_star_prepare_congruence(Star(a.1), Star(b.1));
}

pub broadcast proof fn lemma_repeat_n_serializer_congruence<A, B, N1, N2>(
    a: RepeatN<A, N1>,
    b: RepeatN<B, N2>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    N1: AsLen,
    N2: AsLen,

    requires
        serializer_congruent(a.1, b.1),
        a.0.as_nat() == b.0.as_nat(),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    reveal(<Star::<_> as SpecSerializer>::spec_serialize);
    broadcast use lemma_serializer_congruent_serialize;

    lemma_repeat_n_prepare_congruence(a, b);
    lemma_star_serializer_congruence(Star(a.1), Star(b.1));
    assert forall|vs: Seq<A::Val>| #[trigger] a.spec_serialize(vs) == b.spec_serialize(vs) by {
        lemma_star_serialize_congruence_rec(a.1, b.1, vs);
    }
}

pub broadcast proof fn lemma_array_prepare_congruence<A, B, const N: usize>(
    a: Array<N, A>,
    b: Array<N, B>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_repeat_n_prepare_congruence(RepeatN(N, a.0), RepeatN(N, b.0));
}

pub broadcast proof fn lemma_array_serializer_congruence<A, B, const N: usize>(
    a: Array<N, A>,
    b: Array<N, B>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_array_prepare_congruence(a, b);
    lemma_repeat_n_serializer_congruence(RepeatN(N, a.0), RepeatN(N, b.0));
}

pub broadcast proof fn lemma_optional_end_prepare_congruence<A, B>(
    a: OptionalEnd<A>,
    b: OptionalEnd<B>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_prepare_congruent_reflexive(Eof);
    lemma_optional_prepare_congruence(Optional(a.0, Eof), Optional(b.0, Eof));
}

pub broadcast proof fn lemma_optional_end_serializer_congruence<A, B>(
    a: OptionalEnd<A>,
    b: OptionalEnd<B>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_optional_end_prepare_congruence(a, b);
    lemma_serializer_congruent_reflexive(Eof);
    lemma_optional_serializer_congruence(Optional(a.0, Eof), Optional(b.0, Eof));
}

pub broadcast proof fn lemma_repeat_till_end_prepare_congruence<A, B>(
    a: RepeatTillEnd<A>,
    b: RepeatTillEnd<B>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,

    requires
        prepare_congruent(a.0, b.0),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_prepare_congruent_reflexive(Eof);
    lemma_repeat_prepare_congruence(Repeat(a.0, Eof), Repeat(b.0, Eof));
}

pub broadcast proof fn lemma_repeat_till_end_serializer_congruence<A, B>(
    a: RepeatTillEnd<A>,
    b: RepeatTillEnd<B>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,

    requires
        serializer_congruent(a.0, b.0),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_repeat_till_end_prepare_congruence(a, b);
    lemma_serializer_congruent_reflexive(Eof);
    lemma_repeat_serializer_congruence(Repeat(a.0, Eof), Repeat(b.0, Eof));
}

pub broadcast proof fn lemma_preceded_prepare_congruence<A1, A2, B1, B2, const CHECK: bool>(
    a: Preceded<A1, A1::Val, B1, CHECK>,
    b: Preceded<A2, A1::Val, B2, CHECK>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.a, b.a),
        prepare_congruent(a.b, b.b),
        a.a_val == b.a_val,
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_preceded_serializer_congruence<A1, A2, B1, B2, const CHECK: bool>(
    a: Preceded<A1, A1::Val, B1, CHECK>,
    b: Preceded<A2, A1::Val, B2, CHECK>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.a, b.a),
        serializer_congruent(a.b, b.b),
        a.a_val == b.a_val,
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_preceded_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_terminated_prepare_congruence<A1, A2, B1, B2, const CHECK: bool>(
    a: Terminated<A1, B1, B1::Val, CHECK>,
    b: Terminated<A2, B2, B1::Val, CHECK>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.a, b.a),
        prepare_congruent(a.b, b.b),
        a.b_val == b.b_val,
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_terminated_serializer_congruence<A1, A2, B1, B2, const CHECK: bool>(
    a: Terminated<A1, B1, B1::Val, CHECK>,
    b: Terminated<A2, B2, B1::Val, CHECK>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.a, b.a),
        serializer_congruent(a.b, b.b),
        a.b_val == b.b_val,
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_terminated_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_and_then_prepare_congruence<A1, A2, B1, B2>(
    a: AndThen<A1, B1>,
    b: AndThen<A2, B2>,
) where
    A1: BytesCombinator + Consistency<Val = Seq<u8>>,
    A2: BytesCombinator + Consistency<Val = Seq<u8>>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_and_then_serializer_congruence<A1, A2, B1, B2>(
    a: AndThen<A1, B1>,
    b: AndThen<A2, B2>,
) where
    A1: BytesCombinator + Consistency<Val = Seq<u8>> + SpecSerializer<SVal = Seq<u8>>,
    A2: BytesCombinator + Consistency<Val = Seq<u8>> + SpecSerializer<SVal = Seq<u8>>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_and_then_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_alt_prepare_congruence<A1, A2, B1, B2, const NONDETERMINISTIC: bool>(
    a: Alt<A1, B1, NONDETERMINISTIC>,
    b: Alt<A2, B2, NONDETERMINISTIC>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_alt_serializer_congruence<
    A1,
    A2,
    B1,
    B2,
    const NONDETERMINISTIC: bool,
>(a: Alt<A1, B1, NONDETERMINISTIC>, b: Alt<A2, B2, NONDETERMINISTIC>) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    broadcast use lemma_serializer_congruent_prepare;
    broadcast use lemma_prepare_congruent_consistent;
    broadcast use lemma_serializer_congruent_serialize;

    lemma_alt_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_mapped_prepare_congruence<A, B, M1, M2>(
    a: Mapped<A, M1>,
    b: Mapped<B, M2>,
) where
    A: Consistency + SpecByteLen<T = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val>,
    M1: crate::combinators::mapped::spec::SpecMapper<In = A::Val>,
    M2: crate::combinators::mapped::spec::SpecMapper<In = A::Val, Out = M1::Out>,

    requires
        prepare_congruent(a.inner, b.inner),
        forall|v: M1::Out| #[trigger] a.mapper.spec_map_rev(v) == b.mapper.spec_map_rev(v),
        forall|v: M1::Out| #[trigger] a.mapper.wf_out(v) <==> b.mapper.wf_out(v),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
}

pub broadcast proof fn lemma_mapped_serializer_congruence<A, B, M1, M2>(
    a: Mapped<A, M1>,
    b: Mapped<B, M2>,
) where
    A: Consistency + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    B: Consistency<Val = A::Val> + SpecByteLen<T = A::Val> + SpecSerializer<SVal = A::Val>,
    M1: crate::combinators::mapped::spec::SpecMapper<In = A::Val>,
    M2: crate::combinators::mapped::spec::SpecMapper<In = A::Val, Out = M1::Out>,

    requires
        serializer_congruent(a.inner, b.inner),
        forall|v: M1::Out| #[trigger] a.mapper.spec_map_rev(v) == b.mapper.spec_map_rev(v),
        forall|v: M1::Out| #[trigger] a.mapper.wf_out(v) <==> b.mapper.wf_out(v),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_mapped_prepare_congruence(a, b);
}

// ====================================================
// Dependent and sum formats
// ====================================================
pub broadcast proof fn lemma_bind_prepare_congruence<A1, A2, B1, B2>(
    a: Bind<A1, B1>,
    b: Bind<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: SpecMap<Input = A1::Val>,
    B2: SpecMap<Input = A1::Val>,
    B1::Output: Consistency + SpecByteLen<T = <B1::Output as Consistency>::Val>,
    B2::Output: Consistency<Val = <B1::Output as Consistency>::Val> + SpecByteLen<
        T = <B1::Output as Consistency>::Val,
    >,

    requires
        prepare_congruent(a.0, b.0),
        forall|key: A1::Val| #[trigger] prepare_congruent(a.1.spec_map(key), b.1.spec_map(key)),
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    broadcast use lemma_prepare_congruent_consistent;
    broadcast use lemma_prepare_congruent_byte_len;

}

pub broadcast proof fn lemma_bind_serializer_congruence<A1, A2, B1, B2>(
    a: Bind<A1, B1>,
    b: Bind<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: SpecMap<Input = A1::Val>,
    B2: SpecMap<Input = A1::Val>,
    B1::Output: Consistency + SpecByteLen<T = <B1::Output as Consistency>::Val> + SpecSerializer<
        SVal = <B1::Output as Consistency>::Val,
    >,
    B2::Output: Consistency<Val = <B1::Output as Consistency>::Val> + SpecByteLen<
        T = <B1::Output as Consistency>::Val,
    > + SpecSerializer<SVal = <B1::Output as Consistency>::Val>,

    requires
        serializer_congruent(a.0, b.0),
        forall|key: A1::Val| #[trigger] serializer_congruent(a.1.spec_map(key), b.1.spec_map(key)),
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    broadcast use lemma_serializer_congruent_prepare;
    broadcast use lemma_serializer_congruent_serialize;

    lemma_bind_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_sum_prepare_congruence<A1, A2, B1, B2>(
    a: Sum<A1, B1>,
    b: Sum<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val>,

    requires
        match (a, b) {
            (Sum::Inl(a), Sum::Inl(b)) => prepare_congruent(a, b),
            (Sum::Inr(a), Sum::Inr(b)) => prepare_congruent(a, b),
            _ => false,
        },
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    broadcast use lemma_prepare_congruent_consistent;
    broadcast use lemma_prepare_congruent_byte_len;

}

pub broadcast proof fn lemma_sum_serializer_congruence<A1, A2, B1, B2>(
    a: Sum<A1, B1>,
    b: Sum<A2, B2>,
) where
    A1: Consistency + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    A2: Consistency<Val = A1::Val> + SpecByteLen<T = A1::Val> + SpecSerializer<SVal = A1::Val>,
    B1: Consistency + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,
    B2: Consistency<Val = B1::Val> + SpecByteLen<T = B1::Val> + SpecSerializer<SVal = B1::Val>,

    requires
        match (a, b) {
            (Sum::Inl(a), Sum::Inl(b)) => serializer_congruent(a, b),
            (Sum::Inr(a), Sum::Inr(b)) => serializer_congruent(a, b),
            _ => false,
        },
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    broadcast use lemma_serializer_congruent_prepare;
    broadcast use lemma_serializer_congruent_serialize;

    lemma_sum_prepare_congruence(a, b);
}

// ====================================================
// Prefix/suffix tagging (derived through Const + Preceded/Terminated)
// ====================================================
pub broadcast proof fn lemma_prefix_tagged_parser_congruence<Tg1, Tg2, Of1, Of2>(
    a: PrefixTagged<Tg1, Tg1::T, Of1>,
    b: PrefixTagged<Tg2, Tg1::T, Of2>,
) where
    Tg1: SpecByteLen + SpecParser<PVal = Tg1::T>,
    Tg2: SpecByteLen<T = Tg1::T> + SpecParser<PVal = Tg1::T>,
    Of1: SpecParser,
    Of2: SpecParser<PVal = Of1::PVal>,

    requires
        parser_congruent(a.0, b.0),
        parser_congruent(a.2, b.2),
        a.1 == b.1,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    lemma_const_parser_congruence(Const(a.0, a.1), Const(b.0, b.1));
    lemma_preceded_parser_congruence(
        Preceded::<_, _, _, false> { a: Const(a.0, a.1), b: a.2, a_val: a.1 },
        Preceded::<_, _, _, false> { a: Const(b.0, b.1), b: b.2, a_val: b.1 },
    );
}

pub broadcast proof fn lemma_suffix_tagged_parser_congruence<Tg1, Tg2, Of1, Of2>(
    a: SuffixTagged<Of1, Tg1, Tg1::T>,
    b: SuffixTagged<Of2, Tg2, Tg1::T>,
) where
    Tg1: SpecByteLen + SpecParser<PVal = Tg1::T>,
    Tg2: SpecByteLen<T = Tg1::T> + SpecParser<PVal = Tg1::T>,
    Of1: SpecParser,
    Of2: SpecParser<PVal = Of1::PVal>,

    requires
        parser_congruent(a.0, b.0),
        parser_congruent(a.1, b.1),
        a.2 == b.2,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    lemma_const_parser_congruence(Const(a.1, a.2), Const(b.1, b.2));
    lemma_terminated_parser_congruence(
        Terminated::<_, _, _, false> { a: a.0, b: Const(a.1, a.2), b_val: a.2 },
        Terminated::<_, _, _, false> { a: b.0, b: Const(b.1, b.2), b_val: b.2 },
    );
}

pub broadcast proof fn lemma_prefix_tagged_prepare_congruence<Tg1, Tg2, Of1, Of2>(
    a: PrefixTagged<Tg1, Tg1::Val, Of1>,
    b: PrefixTagged<Tg2, Tg1::Val, Of2>,
) where
    Tg1: Consistency + SpecByteLen<T = Tg1::Val>,
    Tg2: Consistency<Val = Tg1::Val> + SpecByteLen<T = Tg1::Val>,
    Of1: Consistency + SpecByteLen<T = Of1::Val>,
    Of2: Consistency<Val = Of1::Val> + SpecByteLen<T = Of1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.2, b.2),
        a.1 == b.1,
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_const_prepare_congruence(Const(a.0, a.1), Const(b.0, b.1));
    lemma_preceded_prepare_congruence(
        Preceded::<_, _, _, false> { a: Const(a.0, a.1), b: a.2, a_val: a.1 },
        Preceded::<_, _, _, false> { a: Const(b.0, b.1), b: b.2, a_val: b.1 },
    );
}

pub broadcast proof fn lemma_prefix_tagged_serializer_congruence<Tg1, Tg2, Of1, Of2>(
    a: PrefixTagged<Tg1, Tg1::Val, Of1>,
    b: PrefixTagged<Tg2, Tg1::Val, Of2>,
) where
    Tg1: Consistency + SpecByteLen<T = Tg1::Val> + SpecSerializer<SVal = Tg1::Val>,
    Tg2: Consistency<Val = Tg1::Val> + SpecByteLen<T = Tg1::Val> + SpecSerializer<SVal = Tg1::Val>,
    Of1: Consistency + SpecByteLen<T = Of1::Val> + SpecSerializer<SVal = Of1::Val>,
    Of2: Consistency<Val = Of1::Val> + SpecByteLen<T = Of1::Val> + SpecSerializer<SVal = Of1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.2, b.2),
        a.1 == b.1,
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_const_serializer_congruence(Const(a.0, a.1), Const(b.0, b.1));
    lemma_preceded_serializer_congruence(
        Preceded::<_, _, _, false> { a: Const(a.0, a.1), b: a.2, a_val: a.1 },
        Preceded::<_, _, _, false> { a: Const(b.0, b.1), b: b.2, a_val: b.1 },
    );
    lemma_prefix_tagged_prepare_congruence(a, b);
}

pub broadcast proof fn lemma_suffix_tagged_prepare_congruence<Tg1, Tg2, Of1, Of2>(
    a: SuffixTagged<Of1, Tg1, Tg1::Val>,
    b: SuffixTagged<Of2, Tg2, Tg1::Val>,
) where
    Tg1: Consistency + SpecByteLen<T = Tg1::Val>,
    Tg2: Consistency<Val = Tg1::Val> + SpecByteLen<T = Tg1::Val>,
    Of1: Consistency + SpecByteLen<T = Of1::Val>,
    Of2: Consistency<Val = Of1::Val> + SpecByteLen<T = Of1::Val>,

    requires
        prepare_congruent(a.0, b.0),
        prepare_congruent(a.1, b.1),
        a.2 == b.2,
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    lemma_const_prepare_congruence(Const(a.1, a.2), Const(b.1, b.2));
    lemma_terminated_prepare_congruence(
        Terminated::<_, _, _, false> { a: a.0, b: Const(a.1, a.2), b_val: a.2 },
        Terminated::<_, _, _, false> { a: b.0, b: Const(b.1, b.2), b_val: b.2 },
    );
}

pub broadcast proof fn lemma_suffix_tagged_serializer_congruence<Tg1, Tg2, Of1, Of2>(
    a: SuffixTagged<Of1, Tg1, Tg1::Val>,
    b: SuffixTagged<Of2, Tg2, Tg1::Val>,
) where
    Tg1: Consistency + SpecByteLen<T = Tg1::Val> + SpecSerializer<SVal = Tg1::Val>,
    Tg2: Consistency<Val = Tg1::Val> + SpecByteLen<T = Tg1::Val> + SpecSerializer<SVal = Tg1::Val>,
    Of1: Consistency + SpecByteLen<T = Of1::Val> + SpecSerializer<SVal = Of1::Val>,
    Of2: Consistency<Val = Of1::Val> + SpecByteLen<T = Of1::Val> + SpecSerializer<SVal = Of1::Val>,

    requires
        serializer_congruent(a.0, b.0),
        serializer_congruent(a.1, b.1),
        a.2 == b.2,
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    lemma_const_serializer_congruence(Const(a.1, a.2), Const(b.1, b.2));
    lemma_terminated_serializer_congruence(
        Terminated::<_, _, _, false> { a: a.0, b: Const(a.1, a.2), b_val: a.2 },
        Terminated::<_, _, _, false> { a: b.0, b: Const(b.1, b.2), b_val: b.2 },
    );
    lemma_suffix_tagged_prepare_congruence(a, b);
}

// ====================================================
// Bit-field mapping
// ====================================================
pub broadcast proof fn lemma_bits_parser_congruence<R1, R2, Tuple, Nominal>(
    a: Bits<R1, Tuple, Nominal>,
    b: Bits<R2, Tuple, Nominal>,
) where
    R1: SpecByteLen + SpecParser<PVal = R1::T>,
    R2: SpecByteLen<T = R1::T> + SpecParser<PVal = R1::T>,

    requires
        parser_congruent(a.repr, b.repr),
        a.unpack == b.unpack,
        a.pack == b.pack,
        a.refinement == b.refinement,
        a.ctor == b.ctor,
        a.dtor == b.dtor,
        a.consistent == b.consistent,
    ensures
        #[trigger] parser_congruent(a, b),
{
    reveal(parser_congruent);
    broadcast use lemma_parser_congruent_apply;

}

pub broadcast proof fn lemma_bits_prepare_congruence<R1, R2, Tuple, Nominal>(
    a: Bits<R1, Tuple, Nominal>,
    b: Bits<R2, Tuple, Nominal>,
) where
    R1: SpecByteLen + Consistency<Val = R1::T>,
    R2: SpecByteLen<T = R1::T> + Consistency<Val = R1::T>,

    requires
        prepare_congruent(a.repr, b.repr),
        a.unpack == b.unpack,
        a.pack == b.pack,
        a.refinement == b.refinement,
        a.ctor == b.ctor,
        a.dtor == b.dtor,
        a.consistent == b.consistent,
    ensures
        #[trigger] prepare_congruent(a, b),
{
    reveal(prepare_congruent);
    broadcast use lemma_prepare_congruent_consistent;
    broadcast use lemma_prepare_congruent_byte_len;

}

pub broadcast proof fn lemma_bits_serializer_congruence<R1, R2, Tuple, Nominal>(
    a: Bits<R1, Tuple, Nominal>,
    b: Bits<R2, Tuple, Nominal>,
) where
    R1: SpecByteLen + Consistency<Val = R1::T> + SpecSerializer<SVal = R1::T>,
    R2: SpecByteLen<T = R1::T> + Consistency<Val = R1::T> + SpecSerializer<SVal = R1::T>,

    requires
        serializer_congruent(a.repr, b.repr),
        a.unpack == b.unpack,
        a.pack == b.pack,
        a.refinement == b.refinement,
        a.ctor == b.ctor,
        a.dtor == b.dtor,
        a.consistent == b.consistent,
    ensures
        #[trigger] serializer_congruent(a, b),
{
    reveal(serializer_congruent);
    broadcast use lemma_serializer_congruent_prepare;
    broadcast use lemma_serializer_congruent_serialize;

    lemma_bits_prepare_congruence(a, b);
}

// ====================================================
// Opt-in broadcast groups
// ====================================================
pub broadcast group parser_congruence_lemmas {
    lemma_parser_congruent_intro,
    lemma_ref_fn_parser_congruence,
    lemma_parser_congruent_reflexive,
    lemma_parser_congruent_apply,
    lemma_exact_len_parser_congruence,
    lemma_pair_parser_congruence,
    lemma_ref_parser_congruence,
    lemma_named_parser_congruence,
    lemma_star_parser_congruence,
    lemma_repeat_parser_congruence,
    lemma_repeat_till_end_parser_congruence,
    lemma_repeat_n_parser_congruence,
    lemma_array_parser_congruence,
    lemma_and_then_parser_congruence,
    lemma_mapped_parser_congruence,
    lemma_refined_parser_congruence,
    lemma_const_parser_congruence,
    lemma_cond_parser_congruence,
    lemma_choice_parser_congruence,
    lemma_alt_parser_congruence,
    lemma_sum_parser_congruence,
    lemma_opt_parser_congruence,
    lemma_optional_parser_congruence,
    lemma_optional_end_parser_congruence,
    lemma_preceded_parser_congruence,
    lemma_terminated_parser_congruence,
    lemma_bind_parser_congruence,
    lemma_prefix_tagged_parser_congruence,
    lemma_suffix_tagged_parser_congruence,
    lemma_bits_parser_congruence,
}

pub broadcast group prepare_congruence_lemmas {
    lemma_prepare_congruent_intro,
    lemma_prepare_congruent_reflexive,
    lemma_prepare_congruent_consistent,
    lemma_prepare_congruent_byte_len,
    lemma_exact_len_prepare_congruence,
    lemma_refined_prepare_congruence,
    lemma_cond_prepare_congruence,
    lemma_const_prepare_congruence,
    lemma_opt_prepare_congruence,
    lemma_ref_prepare_congruence,
    lemma_named_prepare_congruence,
    lemma_star_prepare_congruence,
    lemma_pair_prepare_congruence,
    lemma_choice_prepare_congruence,
    lemma_optional_prepare_congruence,
    lemma_repeat_prepare_congruence,
    lemma_repeat_n_prepare_congruence,
    lemma_array_prepare_congruence,
    lemma_optional_end_prepare_congruence,
    lemma_repeat_till_end_prepare_congruence,
    lemma_preceded_prepare_congruence,
    lemma_terminated_prepare_congruence,
    lemma_and_then_prepare_congruence,
    lemma_alt_prepare_congruence,
    lemma_mapped_prepare_congruence,
    lemma_bind_prepare_congruence,
    lemma_sum_prepare_congruence,
    lemma_prefix_tagged_prepare_congruence,
    lemma_suffix_tagged_prepare_congruence,
    lemma_bits_prepare_congruence,
}

pub broadcast group serializer_congruence_lemmas {
    lemma_serializer_congruent_intro,
    lemma_serializer_congruent_reflexive,
    lemma_serializer_congruent_prepare,
    lemma_serializer_congruent_serialize,
    lemma_exact_len_serializer_congruence,
    lemma_refined_serializer_congruence,
    lemma_cond_serializer_congruence,
    lemma_const_serializer_congruence,
    lemma_opt_serializer_congruence,
    lemma_ref_serializer_congruence,
    lemma_named_serializer_congruence,
    lemma_star_serializer_congruence,
    lemma_pair_serializer_congruence,
    lemma_choice_serializer_congruence,
    lemma_optional_serializer_congruence,
    lemma_repeat_serializer_congruence,
    lemma_repeat_n_serializer_congruence,
    lemma_array_serializer_congruence,
    lemma_optional_end_serializer_congruence,
    lemma_repeat_till_end_serializer_congruence,
    lemma_preceded_serializer_congruence,
    lemma_terminated_serializer_congruence,
    lemma_and_then_serializer_congruence,
    lemma_alt_serializer_congruence,
    lemma_mapped_serializer_congruence,
    lemma_bind_serializer_congruence,
    lemma_sum_serializer_congruence,
    lemma_prefix_tagged_serializer_congruence,
    lemma_suffix_tagged_serializer_congruence,
    lemma_bits_serializer_congruence,
}

} // verus!
