use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::BytesN;
use vest::regular::choice::Opt;
use vest::regular::choice::OrdChoice;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vstd::prelude::*;

verus! {

exec fn parse_opt(x: usize) -> Result<(), Error>
    requires x > 0
 {
    let msg1 = Opt::new(((Tag::new(U8, 1), BytesN::<0>), Bytes(3)));
    let msg2 = Opt::new(Bytes(x));
    let msg3 = Opt::new(OrdChoice::new(Tag::new(U8, 1u8), Tag::new(U8, 2u8)));
    let mut data1 = my_vec![1u8, 0x40u8, 0xE2u8, 0x01u8, 0x00u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8];
    let (n1, val1) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg1, data1.as_slice())?;
    Ok(())
}

} // verus!
