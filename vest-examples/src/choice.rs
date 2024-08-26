use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::Bytes;
use vest::regular::bytes_n::BytesN;
use vest::regular::choice::Either;
use vest::regular::choice::*;
use vest::regular::tag::*;
use vest::regular::tail::Tail;
use vest::regular::uints::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

broadcast use vest::regular::uints::size_of_facts;

exec fn disjoint_example() {
    let i1 = U8;
    let i2 = U16;
    let c1 = Tag::new(U32, 32000);
    let c2 = Tag::new(U32, 32001);
    let c3 = Tag::new(U8, 0);
    let c4 = Tag::new(U8, 1);
    let c5 = Tag::new(U8, 2);
    let c6 = Tag::new(U8, 3);
    // let ord_choice1 = OrdChoice::new(c1, i1); // err: DisjointSpecCombinator not implemented
    // let ord_choice2 = OrdChoice::new(c1.clone(), c1.clone()); // err: not disjoint
    let ord_choice3 = OrdChoice::new(Tag::new(U8, 1), Tag::new(U8, 2));  // ok
    let ord_choice4 = OrdChoice::new(Tag::new(U16, 1234), Tag::new(U16, 4321));  // ok
    // let ord_choice5 = OrdChoice::new((c1, i1), (Tag::new(U32, 32000), i2)); // err: not disjoint
    let ord_choice6 = OrdChoice::new((c1.clone(), i1.clone()), (c2.clone(), i2.clone()));  // ok
    let ord_choice7 = OrdChoice::new(
        ((c1.clone(), i1.clone()), U32),
        ((c2.clone(), i2.clone()), U16),
    );  // ok
    let ord_choice8 = OrdChoice::new(
        (c1.clone(), (i1.clone(), U32)),
        (c2.clone(), (i2.clone(), U16)),
    );  // ok
    // let ord_choice9 = OrdChoice::new(OrdChoice::new(OrdChoice::new(c5.clone(), c4.clone()), c5.clone()), c6.clone()); // err: not disjoint
    let ord_choice10 = OrdChoice::new(
        OrdChoice::new(OrdChoice::new(c3.clone(), c4.clone()), c5.clone()),
        c6.clone(),
    );  // ok
}

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
exec fn choice_parse_serialize() -> Result<(), ()> {
    let c1 = Tag::new(U8, 1);
    let c2 = Tag::new(U8, 2);
    let c3 = Tag::new(U8, 3);
    let c4 = Tag::new(U8, 4);
    let g1 = (Bytes(4), Tail);
    let g2 = (U32, (U16, U8));
    let g3 = (Tag::new(U8, 10), U32);
    let g4 = (BytesN::<12>, (U16, (U8, U8)));
    // let ord_choice0 = OrdChoice::new(c1.clone(), OrdChoice::new(c2.clone(), OrdChoice::new(c3.clone(), c4.clone())));
    let ord_choice1 = OrdChoice::new(
        OrdChoice::new(OrdChoice::new((c1, g1), (c2, g2)), (c3, g3)),
        (c4, g4),
    );
    let mut data1 =
        my_vec![1u8, 0x10u8, 0x11u8, 0x12u8, 0x13u8, 0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8];
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n1, val1) = ord_choice1.parse(data1.as_slice())?;
    let len1 = ord_choice1.serialize(val1, &mut s1, 0)?;
    proof {
        ord_choice1.theorem_parse_serialize_roundtrip(data1@);
        assert(n1 == 10);
        assert(data1@.subrange(0, n1 as int) == s1@.subrange(0, len1 as int));
        assert(s1@.subrange(0, len1 as int) == seq![
            1u8,
            0x10u8,
            0x11u8,
            0x12u8,
            0x13u8,
            0x14u8,
            0x15u8,
            0x16u8,
            0x17u8,
            0x18u8,
        ]);
    }
    let mut data2 =
        my_vec![4u8, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0xA0, 0xB1, 0xC2, 0x00, 0x00, 0x00];
    let mut s2 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n2, val2) = ord_choice1.parse(data2.as_slice())?;
    let len2 = ord_choice1.serialize(val2, &mut s2, 0)?;
    proof {
        ord_choice1.theorem_parse_serialize_roundtrip(data2@);
        assert(n2 == 17);
        assert(data2@.subrange(0, n2 as int) == s2@.subrange(0, len2 as int));
        assert(s2@.subrange(0, len2 as int) == seq![
            4u8,
            0,
            1,
            2,
            3,
            4,
            5,
            6,
            7,
            8,
            9,
            10,
            11,
            0xA0,
            0xB1,
            0xC2,
            0x00,
        ]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
exec fn choice_serialize_parse() -> Result<(), ()> {
    let c1 = Tag::new(U8, 1);
    let c2 = Tag::new(U8, 2);
    let c3 = Tag::new(U8, 3);
    let c4 = Tag::new(U8, 4);
    let g1 = (Bytes(4), Tail);
    let g2 = (U32, (U16, U8));
    let g3 = (Tag::new(U8, 10), U32);
    let g4 = (BytesN::<12>, (U16, (U8, U8)));
    let ord_choice1 = OrdChoice::new(
        OrdChoice::new(OrdChoice::new((c1, g1), (c2, g2)), (c3, g3)),
        (c4, g4),
    );
    let vec1 = my_vec![0x10u8, 0x11u8, 0x12u8, 0x13u8];
    let vec2 = my_vec![0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8];
    let val1 = Either::Left(Either::Left(Either::Left(((), (vec1.as_slice(), vec2.as_slice())))));
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len1 = ord_choice1.serialize(val1, &mut s1, 0)?;
    let (n1, val1_) = ord_choice1.parse(slice_subrange(s1.as_slice(), 0, len1))?;
    assert(val1_ is Left);
    proof {
        ord_choice1@.theorem_serialize_parse_roundtrip(val1@);
        assert(n1 == len1);
        // assert(val1@ == val1_@); // rlimit exceeded
        // match val1_@ {
        //     Either::Left(Either::Left(Either::Left(((), (v1, v2))))) => {
        //         assert(v1 == seq![0x10u8, 0x11u8, 0x12u8, 0x13u8]);
        //         assert(v2 == seq![0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8]);
        //     },
        //     _ => assert(false),
        // }
    }
    let vec3 = my_vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];
    let val2 = Either::Right(((), (vec3.as_slice(), (32000u16, (0u8, 0u8)))));
    let mut s2 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len2 = ord_choice1.serialize(val2, &mut s2, 0)?;
    let (n2, val2_) = ord_choice1.parse(slice_subrange(s2.as_slice(), 0, len2))?;
    assert(val2_ is Right);
    proof {
        ord_choice1@.theorem_serialize_parse_roundtrip(val2@);
        assert(n2 == len2);
        // assert(val2@ == val2_@); // rlimit exceeded
        // match val2_@ {
        //     Either::Right(((), (v3, (32000u16, (0u8, 0u8))))) => {
        //         assert(v3 == seq![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
        //     },
        //     _ => assert(false),
        // }
    }
    Ok(())
}

} // verus!
