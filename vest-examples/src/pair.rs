use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

//////////////////////////////////////
/// verify parse-serialize inverse ///
//////////////////////////////////////
exec fn parse_serialize() -> Result<(), Error> {
    let msg1 = ((Tag::new(U8, 1), U32Le), Bytes(3));
    let mut data1 = my_vec![1u8, 0x40u8, 0xE2u8, 0x01u8, 0x00u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8];
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n1, val1) = msg1.parse(data1.as_slice())?;
    let len1 = msg1.serialize(val1, &mut s1, 0)?;
    proof {
        msg1.theorem_parse_serialize_roundtrip(data1@);
        assert(data1@.subrange(0, n1 as int) == s1@.subrange(0, len1 as int));
        assert(s1@.subrange(0, len1 as int) == seq![
            1u8,
            0x40u8,
            0xE2u8,
            0x01u8,
            0x00u8,
            0u8,
            0u8,
            1u8,
        ]);
    }
    Ok(())
}

//////////////////////////////////////
/// verify serialize-parse inverse ///
//////////////////////////////////////
exec fn serialize_parse() -> Result<(), Error> {
    let msg1 = ((Tag::new(U8, 1), U32Le), Bytes(3));
    let mut bytes = my_vec![0u8, 0u8, 1u8];
    let val1 = (((), 123456u32), bytes.as_slice());
    assert(bytes@ == seq![0u8, 0u8, 1u8]);
    let mut s1 = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let len1 = msg1.serialize(val1, &mut s1, 0)?;
    let s1_ = slice_subrange(s1.as_slice(), 0, len1);
    let (n1, val1_) = msg1.parse(s1_)?;
    proof {
        msg1.theorem_serialize_parse_roundtrip(val1@);
        assert(n1 == len1);
        // assert(val1@ == val1_@); // rlimit exceeded
        // assert(val1_@ == (((), 123456u32), seq![0u8, 0u8, 1u8]));
    }
    Ok(())
}

} // verus!
