#![allow(warnings)]
// pub mod repeat;
use vest::{properties::Combinator, regular::repeat::RepeatResult};

use crate::repeat::*;

// Format for:
// ```vest
// opaque_u16_1 = {
//   @l: u16 | { 1..0xffff },
//   data: [u8; @l],
// }
//
// responder_id = opaque_u16_1
//
// responder_id_list = {
//   @l: u16 | { 0..0xffff },
//   list: [u8; @l] >>= Vec<responder_id>,
// }
// ```

// pub struct ResponderIdList<'a> {
//     pub l: u16,
//     pub list: ResponderIdListList<'a>,
// }
// pub type ResponderIdListList<'a> = RepeatResult<ResponderId<'a>>;
// pub type ResponderId<'a> = OpaqueU16<'a>;
// pub struct OpaqueU16<'a> {
//     pub l: u16,
//     pub data: &'a [u8],
// }
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut total_bytes = 0;
    let mut list = Vec::new();
    let mut data_vec: Vec<Vec<u8>> = Vec::new();
    for i in 1..0x160 {
        let mut data = Vec::new();
        for j in 0..i {
            data.push(j as u8);
        }
        data_vec.push(data);
    }
    for data in &data_vec {
        let l = data.len() as u16;
        let opaque_u16 = OpaqueU16 { l, data: &data[..] };
        let responder_id = opaque_u16;
        list.push(responder_id);
        total_bytes += 2 + data.len();
    }
    println!("total_bytes: {}", total_bytes);
    println!("list.len(): {}", list.len());
    let responder_id_list_val = ResponderIdList {
        l: total_bytes as u16,
        list: RepeatResult(list),
    };
    let mut outbuf = vec![0; total_bytes as usize + 2];
    let len = responder_id_list().serialize(&responder_id_list_val, &mut outbuf, 0)?;
    // println!("len: {}", len);

    // let start = std::time::Instant::now();
    // for i in 0..1000000 {
    //     let _ = responder_id_list().serialize(&responder_id_list_val, &mut outbuf, 0)?;
    // }
    // println!("Time elapsed: {} ms", start.elapsed().as_millis());
    // bench_fn(&mut || {
    //     let _ = responder_id_list().serialize(&responder_id_list_val, &mut outbuf, 0)?;
    //     Ok(())
    // })?;

    Ok(())
}

fn bench_fn(
    f: &mut impl FnMut() -> Result<(), Box<dyn std::error::Error>>,
) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    for _ in 0..1000000 {
        f()?;
    }
    println!("Time elapsed: {} ms", start.elapsed().as_millis());

    Ok(())
}
