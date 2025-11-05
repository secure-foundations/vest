use vest_lib::properties::{Combinator, SpecCombinator};
use vstd::prelude::*;

mod vest_mavlink;

use vest_mavlink::*;

verus! {

fn firewall(packet: &[u8]) -> (r: bool)
    requires
        300 <= packet.len() <= usize::MAX,
    // ensures
    //     match spec_mavlink_msg().spec_parse(packet@) {
    //         Some((size, val)) => r == !spec_msg_is_flash_bootloader(val),
    //         None => r == false,
    //     }
{
    let mut len = 0;
    let mut packet_num = 0;

        match parse_mavlink_msg(packet) {
            Ok((_curr_len, msg)) => {
                true
            }
            Err(e) => {
                false
            }
        }
}

// terrain_request = {
// 	lat: u32,  // Latitude of SW corner of first grid
// 	lon: u32,  // Longitude of SW corner of first grid
// 	grid_spacing: u16,  // Grid spacing
// 	mask: u64,  // Bitmask of requested 4x4 grids (row major 8x7 array of grids, 56 bits)
// }
fn test_ser(obuf: &mut Vec<u8>)
    requires old(obuf).len() <= usize::MAX,
{
   let tr = TerrainRequest {
        lat: 123456789,
        lon: 987654321,
        grid_spacing: 100,
        mask: 0b101010,
    };
    let _ = serialize_terrain_request(&tr, obuf, 0);
}


fn foo() {
    assert(1 == 0 + 1);
}

} // verus!
