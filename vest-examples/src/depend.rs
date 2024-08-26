use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::depend::{Depend, SpecDepend};
use vest::regular::uints::*;
use vstd::prelude::*;

verus! {

// pub open spec fn msg1() -> SpecDepend<(U8, U16), (Bytes, Bytes)> {
//     SpecDepend {
//         fst: (U8, U16),
//         snd: |deps|
//             {
//                 let (x, y) = deps;
//                 (Bytes(x as usize), Bytes(y as usize))
//             },
//     }
// }
//
// // doesn't work as Veurs doesn't support existential types (impl Trait) yet
// pub fn mk_msg1() -> (o: Depend<
//     (U8, U16),
//     (Bytes, Bytes),
//     impl Fn((u8, u16)) -> (Bytes, Bytes),
//     >)
//     ensures
//         o@ == msg1(),
// {
//     let ghost spec_snd = |deps|
//         {
//             let (x, y) = deps;
//             (Bytes(x as usize), Bytes(y as usize))
//         };
//     Depend {
//         fst: (U8, U16),
//         snd: (move |deps| -> (o: (Bytes, Bytes))
//             ensures
//                 o@ == spec_snd(deps@),
//             {
//                 let (x, y) = deps;
//                 (Bytes(x as usize), Bytes(y as usize))
//             }),
//         spec_snd: Ghost(spec_snd),
//     }
// }
pub open spec fn spec_parse_msg1(data: Seq<u8>) -> Result<
    (usize, ((u8, u16), (Seq<u8>, Seq<u8>))),
    (),
> {
    SpecDepend {
        fst: (U8, U16),
        snd: |deps|
            {
                let (x, y) = deps;
                (Bytes(x as usize), Bytes(y as usize))
            },
    }.spec_parse(data)
}

pub fn parse_msg1<'a>(data: &'a [u8]) -> (o: Result<(usize, ((u8, u16), (&'a [u8], &'a [u8]))), ()>)
    ensures
        o is Ok ==> o.unwrap()@ == spec_parse_msg1(data@).unwrap(),
        o is Err ==> spec_parse_msg1(data@) is Err,
{
    let ghost spec_snd = |deps|
        {
            let (x, y) = deps;
            (Bytes(x as usize), Bytes(y as usize))
        };
    Depend {
        fst: (U8, U16),
        snd: (|deps| -> (o: (Bytes, Bytes))
            ensures
                o@ == spec_snd(deps@),
            {
                let (x, y) = deps;
                (Bytes(x as usize), Bytes(y as usize))
            }),
        spec_snd: Ghost(spec_snd),
    }.parse(data)
}

pub open spec fn spec_serialize_msg1(v: ((u8, u16), (Seq<u8>, Seq<u8>))) -> Result<Seq<u8>, ()> {
    SpecDepend {
        fst: (U8, U16),
        snd: |deps|
            {
                let (x, y) = deps;
                (Bytes(x as usize), Bytes(y as usize))
            },
    }.spec_serialize(v)
}

pub fn serialize_msg1(v: ((u8, u16), (&[u8], &[u8])), data: &mut Vec<u8>, pos: usize) -> (o: Result<
    usize,
    (),
>)
    ensures
        o is Ok ==> o.unwrap() == spec_serialize_msg1(v@).unwrap().len() && data@ == seq_splice(
            old(data)@,
            pos,
            spec_serialize_msg1(v@).unwrap(),
        ),
{
    let ghost spec_snd = |deps|
        {
            let (x, y) = deps;
            (Bytes(x as usize), Bytes(y as usize))
        };
    Depend {
        fst: (U8, U16),
        snd: (|deps| -> (o: (Bytes, Bytes))
            ensures
                o@ == spec_snd(deps@),
            {
                let (x, y) = deps;
                (Bytes(x as usize), Bytes(y as usize))
            }),
        spec_snd: Ghost(spec_snd),
    }.serialize(v, data, pos)
}

// proof fn test(data: Seq<u8>) {
//     let msg1 = SpecCombinatorFn {
//         parse: |data| spec_parse_msg1(data),
//         serialize: |v| spec_serialize_msg1(v),
//     };
//
//     if let Ok((n, val)) = msg1.spec_parse(data) {
//         if let Ok(s) = msg1.spec_serialize(val) {
//             msg1.spec_parse_serialize(data);
//             assert(data == s);
//         }
//     }
// }
} // verus!
