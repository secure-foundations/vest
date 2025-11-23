#![allow(unused_imports)]
#![allow(warnings)]
use vest_lib::properties::*;
use vest_lib::regular::bytes;
use vest_lib::regular::end::*;
use vest_lib::regular::repetition::RepeatN;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::regular::variant::{Choice, Opt, OptThen};
use vstd::prelude::*;

verus! {

exec fn parse_opt(x: usize) -> Result<(), Error>
    requires
        x > 0,
{
    let msg1 = Opt::new(RepeatN(((Tag::new(U8, 1u8), bytes::Fixed::<0>), bytes::Variable(3)), 2));
    let msg2 = Opt::new(bytes::Variable(x));
    let msg3 = Opt::new(Choice::new(Tag::new(U8, 1u8), Tag::new(U8, 2u8)));
    let mut data1 = vec![1u8, 0x40u8, 0xE2u8, 0x01u8, 0x00u8, 0u8, 0u8, 1u8, 0u8, 0u8, 0u8, 0u8];
    let (n1, val1) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&msg2, data1.as_slice())?;
    Ok(())
}

fn opt_then() {
    let c1 = (Tag::new(U8, 1u8), U8);
    let c2 = (Tag::new(U8, 2u8), U16Le);
    let c3 = (Tag::new(U8, 3u8), U32Le);
    let c1 = OptThen::new(
        c1,
        OptThen::new(
            c2,
            OptThen::new(
                c3,
                End,
            ),
        ),
    );
    assert(c1.requires());
}

} // verus!
