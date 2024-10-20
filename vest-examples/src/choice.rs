use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::Bytes;
use vest::regular::bytes_n::BytesN;
use vest::regular::choice::Either;
use vest::regular::choice::*;
use vest::regular::cond::Cond;
use vest::regular::tag::*;
use vest::regular::tail::Tail;
use vest::regular::uints::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

broadcast use vest::regular::uints::size_of_facts;

exec fn disjoint_examples(a: u32, b: u8) -> Result<(), Error> {
    let c1 = Cond { cond: a == 0 && b == 1, inner: U8 };
    let c2 = Cond { cond: 0 < a && a < 5 && b == 2, inner: U16Le };
    let c3 = Cond { cond: a >= 5 && b == 2, inner: U32Le };

    let choice = ord_choice!(c1, c2, c3);

    let mut data = my_vec![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = choice.parse(data.as_slice())?;
    let len = choice.serialize(val, &mut s, 0)?;

    Ok(())
}

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
exec fn choice_parse_serialize() -> Result<(), Error> {
    let c1 = Tag::new(U8, 1);
    let c2 = Tag::new(U8, 2);
    let c3 = Tag::new(U8, 3);
    let c4 = Tag::new(U8, 4);
    let g1 = (Bytes(4), Tail);
    let g2 = (U32Le, (U16Le, U8));
    let g3 = (Tag::new(U8, 10), U32Le);
    let g4 = (BytesN::<12>, (U16Le, (U8, U8)));
    let ord_choice1 =
        ord_choice!(
        (c1, g1),
        (c2, g2),
        (c3, g3),
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
exec fn choice_serialize_parse() -> Result<(), Error> {
    let c1 = Tag::new(U8, 1);
    let c2 = Tag::new(U8, 2);
    let c3 = Tag::new(U8, 3);
    let c4 = Tag::new(U8, 4);
    let g1 = (Bytes(4), Tail);
    let g2 = (U32Le, (U16Le, U8));
    let g3 = (Tag::new(U8, 10), U32Le);
    let g4 = (BytesN::<12>, (U16Le, (U8, U8)));
    let ord_choice1 =
        ord_choice!(
        (c1, g1),
        (c2, g2),
        (c3, g3),
        (c4, g4),
    );
    let vec1 = my_vec![0x10u8, 0x11u8, 0x12u8, 0x13u8];
    let vec2 = my_vec![0x14u8, 0x15u8, 0x16u8, 0x17u8, 0x18u8];
    let val1 = inj_ord_choice_result!(((), (vec1.as_slice(), vec2.as_slice())), *, *, *);
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
    let val2 = inj_ord_choice_result!(*, *, *, ((), (vec3.as_slice(), (32000u16, (0u8, 0u8)))));
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
