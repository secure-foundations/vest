use crate::combinators::disjoint::*;
use crate::combinators::tuple::Pair;
use crate::combinators::*;
use crate::core::proof::*;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

// Enable all disjointness lemmas
broadcast use {
    lemma_disjoint_const,
    lemma_disjoint_tuple,
    lemma_disjoint_preceded,
    lemma_disjoint_terminated,
    lemma_disjoint_mapped,
    lemma_disjoint_choice,
    lemma_disjoint_optional,
    lemma_disjoint_repeat,
    lemma_disjoint_eof,
    lemma_disjoint_tuple_2,
};

proof fn test_disjointness_tags() {
    let tag1 = Const(U8, 1u8);
    let tag2 = Const(U8, 2u8);
    let tag3 = Const(U8, 3u8);
    let tag4 = Const(U8, 4u8);

    let t1 = Pair(tag1, tag2);
    let t2 = Pair(tag3, tag4);
    let c1 = Choice(t1, t2);
    assert(c1.unambiguous());

    let p1 = Preceded::<_, _, _, false> { a: tag1, b: tag2, a_val: 1u8 };
    assert(p1.unambiguous());

    let term1 = Terminated::<_, _, _, false> { a: tag3, b: tag4, b_val: 4u8 };
    assert(term1.unambiguous());

    let c2 = Choice(p1, term1);
    assert(c2.unambiguous());
}

proof fn test_disjointness_mapped() {
    let eof = Eof;
    let m1 = Mapped { inner: U8, mapper: (|x: u8| x, |x: u8| x) };
    let c3 = Choice(m1, eof);
    assert(c3.unambiguous());
}

proof fn test_disjointness_nested_choice() {
    let tag1 = Const(U8, 1u8);
    let tag2 = Const(U8, 2u8);
    let tag3 = Const(U8, 3u8);
    let tag4 = Const(U8, 4u8);
    let c_left = Choice(tag1, tag2);
    let c_right = Choice(tag3, tag4);
    let c_main = Choice(c_left, c_right);

    assert(c_main.unambiguous());
}

proof fn test_disjointness_optional_chain() {
    let tag1 = Const(U8, 1u8);
    let tag2 = Const(U8, 2u8);
    let opt_chain = Optional(tag1, Optional(tag2, Eof));

    assert(opt_chain.unambiguous());
}

proof fn test_choice_with_repeat() {
    let tag1 = Const(U8, 1u8);
    let tag2 = Const(U8, 2u8);
    let eof = Eof;
    let rep = Repeat(tag1, eof);
    let c = Choice(rep, tag2);

    assert(c.unambiguous());
}

struct Odd;

impl SpecPred<u8> for Odd {
    open spec fn apply(&self, value: u8) -> bool {
        value % 2 != 0
    }
}

struct Even;

impl SpecPred<u8> for Even {
    open spec fn apply(&self, value: u8) -> bool {
        value % 2 == 0
    }
}

proof fn test_disjointness_refined() {
    let odd = Refined(U8, Odd);
    let even = Refined(U8, Even);
    let c = Choice(odd, even);
    assert(c.unambiguous());
}

proof fn test_disjointness_shared_prefix() {
    let tag1 = Const(U8, 1u8);
    let tag2 = Const(U8, 2u8);
    let tag3 = Const(U8, 3u8);
    let c_left = Pair(tag1, Pair(tag2, tag2));
    let c_right = Pair(tag1, Pair(tag2, tag3));
    let c_main = Choice(c_left, c_right);

    assert(c_main.unambiguous());
}

} // verus!
