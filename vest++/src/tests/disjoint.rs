use crate::combinators::disjoint::*;
use crate::combinators::mapped::spec::Mapper;
use crate::combinators::*;
use crate::core::{spec::*, types};
use vstd::prelude::*;

verus! {

// Enable all disjointness lemmas
broadcast use {
    lemma_disjoint_tag,
    lemma_disjoint_tuple,
    lemma_disjoint_preceded,
    lemma_disjoint_terminated,
    lemma_disjoint_mapped,
    lemma_disjoint_choice,
    lemma_disjoint_optional,
    lemma_disjoint_repeat,
    lemma_disjoint_eof,
};

proof fn test_disjointness_tags() {
    let tag1 = Tag { inner: U8, tag: 1u8 };
    let tag2 = Tag { inner: U8, tag: 2u8 };
    let tag3 = Tag { inner: U8, tag: 3u8 };
    let tag4 = Tag { inner: U8, tag: 4u8 };

    let t1 = (tag1, tag2);
    let t2 = (tag3, tag4);
    let c1 = Choice(t1, t2);
    assert(c1.unambiguous());

    assert(().wf());

    let p1 = Preceded(tag1, tag2);
    assert(p1.unambiguous());

    let term1 = Terminated(tag3, tag4);
    assert(term1.unambiguous());

    let c2 = Choice(p1, term1);
    assert(c2.unambiguous());
}

// Mapped helper
struct MyMapper;

impl Mapper for MyMapper {
    type In = u8;

    type Out = u8;

    open spec fn spec_map(&self, i: u8) -> u8 {
        i
    }

    open spec fn spec_map_rev(&self, o: u8) -> u8 {
        o
    }
}

proof fn test_disjointness_mapped() {
    let eof = Eof;
    let m1 = Mapped { inner: U8, mapper: MyMapper };
    let c3 = Choice(m1, eof);
    assert(c3.unambiguous());
}

proof fn test_disjointness_nested_choice() {
    let tag1 = Tag { inner: U8, tag: 1u8 };
    let tag2 = Tag { inner: U8, tag: 2u8 };
    let tag3 = Tag { inner: U8, tag: 3u8 };
    let tag4 = Tag { inner: U8, tag: 4u8 };
    let c_left = Choice(tag1, tag2);
    let c_right = Choice(tag3, tag4);
    let c_main = Choice(c_left, c_right);

    assert(c_main.unambiguous());
}

proof fn test_disjointness_optional_chain() {
    let tag1 = Tag { inner: U8, tag: 1u8 };
    let tag2 = Tag { inner: U8, tag: 2u8 };
    let opt_chain = Optional(tag1, Optional(tag2, Eof));

    assert(opt_chain.unambiguous());
}

proof fn test_choice_with_repeat() {
    let tag1 = Tag { inner: U8, tag: 1u8 };
    let tag2 = Tag { inner: U8, tag: 2u8 };
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
    let odd = Refined { inner: U8, pred: Odd };
    let even = Refined { inner: U8, pred: Even };
    let c = Choice(odd, even);
    assert(c.unambiguous());
}

} // verus!
