use crate::combinators::mapped::exec::*;
use crate::combinators::mapped::spec::*;
use crate::combinators::*;
use crate::combinators::{Mapped, Refined, U8};
use crate::core::exec::parser::Parser;

use crate::core::{proof::*, spec::*};
use vest_derive::DeepView;
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

pub enum MyTag {
    A = 1,
    B = 2,
    C = 3,
}

pub open spec fn is_my_tag_byte(v: u8) -> bool {
    v == 1u8 || v == 2u8 || v == 3u8
}

struct IsMyTagByte;

impl SpecPred<u8> for IsMyTagByte {
    open spec fn apply(&self, v: u8) -> bool {
        is_my_tag_byte(v)
    }
}

struct MyTagMapper;

impl SpecMapper for MyTagMapper {
    type In = u8;

    type Out = MyTag;

    open spec fn spec_map(i: u8) -> MyTag {
        match i {
            1u8 => MyTag::A,
            2u8 => MyTag::B,
            3u8 => MyTag::C,
            _ => arbitrary(),
        }
    }

    open spec fn spec_map_rev(o: MyTag) -> u8 {
        match o {
            MyTag::A => 1u8,
            MyTag::B => 2u8,
            MyTag::C => 3u8,
        }
    }

    open spec fn wf_in(i: Self::In) -> bool {
        is_my_tag_byte(i)
    }
}

impl LossyMapper for MyTagMapper {
    proof fn lemma_sound_mapper(o: MyTag) {
    }

    proof fn lemma_mapper_wf_out_in(o: Self::Out) {
    }
}

impl LosslessMapper for MyTagMapper {
    proof fn lemma_lossless_mapper(i: u8) {
    }

    proof fn lemma_mapper_wf_in_out(i: Self::In) {
    }
}

proof fn my_tag_roundtrip() {
    let my_tag = Mapped {
        inner: Refined { inner: U8, pred: |x| is_my_tag_byte(x) },
        mapper: MyTagMapper,
    };

    assert(my_tag.unambiguous());
    assert(my_tag.consistent(MyTag::A));
    assert(my_tag.consistent(MyTag::B));
    assert(my_tag.consistent(MyTag::C));

    my_tag.theorem_serialize_parse_roundtrip(MyTag::A);
    my_tag.theorem_serialize_parse_roundtrip(MyTag::B);
    my_tag.theorem_serialize_parse_roundtrip(MyTag::C);

    assert(my_tag.spec_parse(seq![1u8]) == Some((1int, MyTag::A)));
    assert(my_tag.spec_parse(seq![2u8]) == Some((1int, MyTag::B)));
    assert(my_tag.spec_parse(seq![3u8]) == Some((1int, MyTag::C)));
}

spec fn test() -> () {
    use super::super::*;
    let m1 = Mapped { inner: U8, mapper: |x: u8| x as u16 };
    let m2 = Mapped { inner: U8, mapper: |x: u16| x as u8 };
    let m3 = Mapped { inner: U8, mapper: (|x: u8| x, |x: u8| x) };
    let m4 = Mapped { inner: Refined { inner: U8, pred: IsMyTagByte }, mapper: MyTagMapper };
    needs_spec_parser(m1);
    needs_spec_serializer(m2);
    needs_spec_combinator(m3);
    needs_spec_combinator(m4);
    ()
}

#[derive(DeepView)]
pub struct Triple<'i> {
    pub a: u8,
    pub b: u8,
    pub c: &'i [u8],
}

// pub struct TripleRefMap;
// pub struct TripleRefMapRev;
// impl SpecMap for TripleRefMap {
//     type SpecI = (u8, (u8, Seq<u8>));
//     type SpecO = TripleSpec;
//     open spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO {
//         TripleSpec { a: i.0, b: i.1.0, c: i.1.1 }
//     }
// }
// impl SpecMap for TripleRefMapRev {
//     type SpecI = TripleSpec;
//     type SpecO = (u8, (u8, Seq<u8>));
//     open spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO {
//         (i.a, (i.b, i.c))
//     }
// }
// impl Map for TripleRefMap {
//     type I = (u8, (u8, &[u8]));
//     type O = TripleRef;
//     fn map(i: Self::I) -> Self::O {
//         TripleRef { a: i.0, b: i.1.0, c: i.1.1 }
//     }
// }

type TripleFmt = Pair<U8, Pair<U8, Fixed<3>>>;

// type TripleSpecInner = (u8, (u8, Seq<u8>));
type TripleSpecInner = <TripleFmt as SpecParser>::PVal;

type TripleInner<'i> = <TripleFmt as Parser<&'i [u8]>>::O;

fn test_map_exec(ibuf: &[u8]) {
    let ghost to_triple_spec = |i: TripleSpecInner|
        {
            let (a, (b, c)) = i;
            TripleSpec { a, b, c }
        };
    let ghost from_triple_spec = |v: TripleSpec| (v.a, (v.b, v.c));
    let fmt = crate::combinators::mapped::Map {
        inner: Pair(U8, Pair(U8, Fixed::<3>)),
        mapper: BiMap(
            FnMap::<_, _, _, spec_fn(TripleSpecInner) -> TripleSpec>::new(
                |i: TripleInner| -> (o: Triple)
                    ensures
                        o.deep_view() == to_triple_spec(i.deep_view()),
                    {
                        let (a, (b, c)) = i;
                        Triple { a, b, c }
                    },
                Ghost(to_triple_spec),
            ),
            FnMap::<_, _, _, spec_fn(TripleSpec) -> TripleSpecInner>::new(
                |i: Triple| -> (o: TripleInner)
                    ensures
                        o.deep_view() == from_triple_spec(i.deep_view()),
                    { (i.a, (i.b, i.c)) },
                Ghost(from_triple_spec),
            ),
        ),
    };

    proof {
        lemma_map_exec_inv::<&[u8], _, _, _>(&fmt);
    }

    let _ = fmt.parse(&ibuf);
}

} // verus!
