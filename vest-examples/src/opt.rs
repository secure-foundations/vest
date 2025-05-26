use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes;
use vest::regular::repetition::RepeatN;
use vest::regular::tag::*;
use vest::regular::uints::*;
use vest::regular::variant::{Choice, Opt};
use vstd::prelude::*;

verus! {

exec fn parse_opt(x: usize) -> Result<(), Error>
    requires
        x > 0,
{
    let msg1 = Opt::new(RepeatN(((Tag::new(U8, 1u8), bytes::Fixed::<0>), bytes::Variable(3)), 2));
    let msg2 = Opt::new(bytes::Variable(x));
    let msg3 = Opt::new(Choice::new(Tag::new(U8, 1u8), Tag::new(U8, 2u8)));
    let mut data1 = my_vec![1u8, 0x40u8, 0xE2u8, 0x01u8, 0x00u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8];
    let (n1, val1) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg2, data1.as_slice())?;
    Ok(())
}

} // verus!
