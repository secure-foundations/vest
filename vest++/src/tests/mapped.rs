use crate::combinators::mapped::spec::{IsoMapper, Mapper};
use crate::combinators::refined::Tag;
use crate::combinators::{BerBool, Mapped, Preceded, Refined, Terminated, U8};

use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

spec fn needs_spec_parser<C: SpecParser>(c: C) -> () {
    ()
}

spec fn needs_spec_serializer<C: SpecSerializerDps>(c: C) -> () {
    ()
}

spec fn needs_spec_combinator<C: SpecCombinator>(c: C) -> () {
    ()
}

spec fn needs_good_combinator<C: GoodCombinator>(c: C) -> () {
    ()
}

struct MyIsoMapper;

impl Mapper for MyIsoMapper {
    type In = u8;

    type Out = u8;

    open spec fn spec_map(&self, i: u8) -> u8 {
        i
    }

    open spec fn spec_map_rev(&self, o: u8) -> u8 {
        o
    }
}

impl IsoMapper for MyIsoMapper {
    proof fn lemma_map_wf(&self, v: Self::In) {
    }

    proof fn lemma_map_rev_wf(&self, v: Self::Out) {
    }

    proof fn lemma_map_iso(&self, i: u8) {
        assert(self.spec_map_rev(self.spec_map(i)) == i);
    }

    proof fn lemma_map_iso_rev(&self, o: u8) {
        assert(self.spec_map(self.spec_map_rev(o)) == o);
    }
}

spec fn test() -> () {
    use super::super::*;
    let m1 = Mapped { inner: U8, mapper: |x: u8| x as u16 };
    let m2 = Mapped { inner: U8, mapper: |x: u16| x as u8 };
    let m3 = Mapped { inner: U8, mapper: (|x: u8| x, |y: u8| y) };
    let m4 = Mapped { inner: U8, mapper: MyIsoMapper };
    needs_spec_parser(m1);
    needs_spec_serializer(m2);
    needs_spec_combinator(m3);
    needs_good_combinator(m4);
    ()
}

} // verus!
