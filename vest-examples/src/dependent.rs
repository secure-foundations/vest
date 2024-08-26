use crate::my_vec;
use vest::properties::*;
use vest::regular::bytes::*;
use vest::regular::dependent::*;
use vest::regular::uints::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

pub struct PairOfDependentBytes;

impl View for PairOfDependentBytes {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl SpecDpdtCombinator for PairOfDependentBytes {
    type Dependencies = (u8, (u16, u32));

    type Dependent = (Bytes, Bytes);

    open spec fn spec_apply_deps(r: Self::Dependencies) -> Self::Dependent {
        let (r0, (_r1, r2)) = r;
        (Bytes(r0 as usize), Bytes(r2 as usize))
    }
}

impl DpdtCombinator for PairOfDependentBytes {
    type Dependencies<'a> = (u8, (u16, u32));

    type DependenciesOwned = (u8, (u16, u32));

    type Dependent = (Bytes, Bytes);

    fn apply_deps<'a>(r: Self::Dependencies<'a>) -> (res: Self::Dependent) {
        let (r0, (_r1, r2)) = r;
        (Bytes(r0 as usize), Bytes(r2 as usize))
    }
}

pub open spec fn msg1() -> Depend<(Int<u8>, (Int<u16>, Int<u32>)), PairOfDependentBytes> {
    Depend(
        (Int::<u8>::spec_new(), (Int::<u16>::spec_new(), Int::<u32>::spec_new())),
        PairOfDependentBytes,
    )
}

pub fn mk_msg1() -> (o: Depend<(Int<u8>, (Int<u16>, Int<u32>)), PairOfDependentBytes>)
    ensures
        o@ == msg1(),
{
    Depend((Int::<u8>::new(), (Int::<u16>::new(), Int::<u32>::new())), PairOfDependentBytes)
}

pub fn parse_serialize(input: &[u8]) -> Result<(), ()>
    requires
        input@ == seq![1u8, 0, 0, 0x00, 0x00, 0x00, 0x05, 0, 0, 0, 0, 0, 0, 0],
{
    let msg = mk_msg1();
    let (n, res) = msg.parse(input)?;
    let mut serialized = my_vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let m = msg.serialize(res, &mut serialized, 0)?;
    proof {
        msg.spec_parse_serialize(input@);
        assert(n == m);
        assert(serialized@.subrange(0, m as int) == input@.subrange(0, n as int));
    }
    Ok(())
}

pub fn serialize_parse(v: ((u8, (u16, u32)), (&[u8], &[u8]))) -> Result<(), ()>
    requires
        v@ == ((1u8, (5u16, 3u32)), (seq![0u8], seq![0u8, 0u8, 0u8])),
{
    let msg = mk_msg1();
    let mut serialized = my_vec![0u8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let m = msg.serialize(v, &mut serialized, 0)?;
    let sub_serialized = slice_subrange(serialized.as_slice(), 0, m);
    let (n, res) = msg.parse(sub_serialized)?;
    proof {
        msg.spec_serialize_parse(v@);
        assert(n == m);
        assert(res@ == v@);
        assert(res@ == ((1u8, (5u16, 3u32)), (seq![0u8], seq![0u8, 0u8, 0u8])));
    }
    Ok(())
}

} // verus!
