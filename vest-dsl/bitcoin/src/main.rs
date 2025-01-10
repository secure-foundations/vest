pub mod transaction_data;
pub mod vest_bitcoin;

use transaction_data::*;
use vest::{
    properties::*,
    regular::{
        choice::{Either, OrdChoice},
        depend::Continuation,
        disjoint::DisjointFrom,
        refined::Refined,
        repeat::{Repeat, RepeatResult},
        star::Star,
        tag::TagPred,
        uints::U8,
    },
};
use vest_bitcoin::*;

use bitcoin::consensus::{Decodable, Encodable};

fn parse_vestbtc_tx() -> Result<(), Box<dyn std::error::Error>> {
    for bytes in transaction_data() {
        let (consumed, parsed_tx) = tx().parse(&bytes).unwrap_or_else(|e| {
            panic!("Failed to parse transaction: {}", e);
        });
        println!("consumed: {}", consumed);
        // println!("parsed_tx: {:?}", parsed_tx);
    }

    Ok(())
}

fn parse_rustbtc_tx() -> Result<(), Box<dyn std::error::Error>> {
    for bytes in transaction_data() {
        let tx = bitcoin::Transaction::consensus_decode(&mut &bytes[..]).unwrap_or_else(|e| {
            panic!("Failed to parse transaction: {}", e);
        });
        // println!("tx: {:?}", tx);
    }

    Ok(())
}

fn serialize_vestbtc_tx() -> Result<(), Box<dyn std::error::Error>> {
    for (i, tx_msg) in vestbtc_transaction_msgs().into_iter().enumerate() {
        let mut buf = vec![0; 4096];
        let len = tx()
            .serialize(tx_msg, &mut buf, 0)
            .unwrap_or_else(|e| panic!("Failed to serialize Handshake: {}", e));
        println!("len: {}", len);
        assert_eq!(&buf[0..len], &transaction_data()[i][0..len]);
    }

    Ok(())
}

fn serialize_rustbtc_tx() -> Result<(), Box<dyn std::error::Error>> {
    for (i, tx_msg) in rustbtc_transaction_msgs().into_iter().enumerate() {
        let mut buf = Vec::with_capacity(4096);
        // let mut buf = vec![0; 4096];
        let len = tx_msg
            .consensus_encode(&mut buf)
            .unwrap_or_else(|e| panic!("Failed to serialize Handshake: {}", e));
        // println!("len: {}", len);
        // assert_eq!(&buf[0..len], &transaction_data()[i][0..len]);
    }

    Ok(())
}

fn transaction_data() -> [&'static [u8]; 8] {
    [TX1, TX2, TX3, TX4, TX5, TX6, TX7, TX8]
}

fn vestbtc_transaction_msgs<'a>() -> [vest_bitcoin::Tx<'a>; 8] {
    transaction_data().map(|bytes| tx().parse(&bytes).unwrap().1)
}

fn rustbtc_transaction_msgs<'a>() -> [bitcoin::Transaction; 8] {
    transaction_data().map(|bytes| bitcoin::Transaction::consensus_decode(&mut &bytes[..]).unwrap())
}

fn hex_to_bytes(hex: &str) -> Vec<u8> {
    hex::decode(hex).unwrap()
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    parse_vestbtc_tx()?;
    // parse_rustbtc_tx()?;
    serialize_vestbtc_tx()?;
    // serialize_rustbtc_tx()?;
    // bench_fn(parse_rustbtc_tx)?;
    // bench_fn(parse_vestbtc_tx)?;
    // bench_fn(serialize_rustbtc_tx)?;
    // bench_fn(serialize_vestbtc_tx)?;
    // test();

    // for hex in transaction_data() {
    //     println!("{:?}", hex_to_bytes(hex));
    // }

    Ok(())
}

fn bench_fn(
    f: impl Fn() -> Result<(), Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    for _ in 0..1000000 {
        f()?;
    }
    println!("Time elapsed: {} ms", start.elapsed().as_millis());

    Ok(())
}

// pub const INSTR_BASE: u8 = 0;
// pub const AUXBLOCK_BEGIN: u8 = 1;
// pub const AUXBLOCK_END: u8 = 11;
//
// #[derive(Debug)]
// struct InstrFmt(Either<u8, Box<AuxBlockFmt>>);
// #[derive(Debug)]
// struct AuxBlockFmt((u8, (RepeatResult<Box<InstrFmt>>, u8)));
//
// impl vstd::view::View for InstrFmt {
//     type V = Self;
// }
// impl vstd::view::View for AuxBlockFmt {
//     type V = Self;
// }
//
// struct InstrCom(
//     pub OrdChoice<Refined<U8, TagPred<u8>>, Box<dyn Continuation<(), Output = AuxBlockCom>>>,
// );
// struct AuxBlockCom(
//     pub  (
//         Refined<U8, TagPred<u8>>,
//         (
//             Star<Box<dyn Continuation<(), Output = InstrCom>>>,
//             Refined<U8, TagPred<u8>>,
//         ),
//     ),
// );
// impl vstd::view::View for InstrCom {
//     type V = Self;
// }
// impl vstd::view::View for AuxBlockCom {
//     type V = Self;
// }
// impl SpecCombinator for InstrCom {
//     type Type = InstrFmt;
// }
// impl SecureSpecCombinator for InstrCom {}
// impl SpecCombinator for AuxBlockCom {
//     type Type = AuxBlockFmt;
// }
// impl SecureSpecCombinator for AuxBlockCom {}
//
// impl DisjointFrom<Refined<U8, TagPred<u8>>> for AuxBlockCom {}
//
// impl<'a> Combinator<&'a [u8], Vec<u8>> for InstrCom {
//     type Type = InstrFmt;
//     fn length(&self) -> Option<usize> {
//         <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
//     }
//     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
//         match <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s) {
//             Ok((n, Either::Left(v))) => Ok((n, InstrFmt(Either::Left(v)))),
//             Ok((n, Either::Right(v))) => Ok((n, InstrFmt(Either::Right(v)))),
//             Err(e) => Err(e),
//         }
//     }
//     fn serialize(
//         &self,
//         v: Self::Type,
//         data: &mut Vec<u8>,
//         pos: usize,
//     ) -> Result<usize, SerializeError> {
//         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v.0, data, pos)
//     }
// }
//
// impl<'a> Combinator<&'a [u8], Vec<u8>> for AuxBlockCom {
//     type Type = AuxBlockFmt;
//     fn length(&self) -> Option<usize> {
//         <_ as Combinator<&[u8], Vec<u8>>>::length(&self.0)
//     }
//     fn parse(&self, s: &'a [u8]) -> Result<(usize, Self::Type), ParseError> {
//         match <_ as Combinator<&[u8], Vec<u8>>>::parse(&self.0, s) {
//             Ok((n, (a, (b, c)))) => Ok((n, AuxBlockFmt((a, (b, c))))),
//             Err(e) => Err(e),
//         }
//     }
//     fn serialize(
//         &self,
//         v: Self::Type,
//         data: &mut Vec<u8>,
//         pos: usize,
//     ) -> Result<usize, SerializeError> {
//         <_ as Combinator<&[u8], Vec<u8>>>::serialize(&self.0, v.0, data, pos)
//     }
// }
//
// struct AuxBlockCont;
// struct InstrCont;
//
// impl Continuation<()> for AuxBlockCont {
//     type Output = AuxBlockCom;
//
//     fn apply(&self, i: ()) -> Self::Output {
//         AuxBlockCom((
//             Refined {
//                 inner: U8,
//                 predicate: TagPred(AUXBLOCK_BEGIN),
//             },
//             (
//                 Star(Box::new(InstrCont)),
//                 Refined {
//                     inner: U8,
//                     predicate: TagPred(AUXBLOCK_END),
//                 },
//             ),
//         ))
//     }
// }
//
// impl Continuation<()> for InstrCont {
//     type Output = InstrCom;
//
//     fn apply(&self, i: ()) -> Self::Output {
//         InstrCom(OrdChoice(
//             Refined {
//                 inner: U8,
//                 predicate: TagPred(INSTR_BASE),
//             },
//             Box::new(AuxBlockCont),
//         ))
//     }
// }
//
// fn test() {
//     // let buf = vec![0x00];
//     let buf = vec![0x01, 0, 0, 0x01, 0, 0, 0, 0x0B, 0, 0x0B];
//     let aux_block = AuxBlockCont.apply(());
//     let instr = InstrCont.apply(());
//     let (consumed, parsed) = instr.parse(&buf).unwrap_or_else(|e| {
//         panic!("Failed to parse: {}", e);
//     });
//     println!("consumed: {}", consumed);
//     println!("parsed: {:?}", parsed);
// }
//
// // fn instr<'a>() -> InstrCom {
// //     InstrCom(OrdChoice(
// //         Refined {
// //             inner: U8,
// //             predicate: TagPred(INSTR_BASE),
// //         },
// //         Box::new(aux_block()),
// //     ))
// // }
// //
// // fn aux_block<'a>() -> AuxBlockCom {
// //     AuxBlockCom((
// //         Refined {
// //             inner: U8,
// //             predicate: TagPred(AUXBLOCK_BEGIN),
// //         },
// //         (
// //             Star(Box::new(instr())),
// //             Refined {
// //                 inner: U8,
// //                 predicate: TagPred(AUXBLOCK_END),
// //             },
// //         ),
// //     ))
// // }
