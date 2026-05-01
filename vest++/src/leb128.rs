use crate::{
    combinators::{
        mapped::spec::SpecMapper,
        recursive::{BundledSpecs, SpecRecBody},
        Alt, Fix, Mapped, Pair, Refined, U8,
    },
    core::spec::*,
};
use vstd::arithmetic::power::*;
use vstd::prelude::*;

verus! {

pub const LEB128_CONT_BIT: u8 = 0x80;

pub struct U8FromToNat;

impl SpecMapper for U8FromToNat {
    type In = u8;

    type Out = nat;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        i < LEB128_CONT_BIT
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o < LEB128_CONT_BIT
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        i as nat
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        o as u8
    }
}

pub struct PairFromToNat;

impl SpecMapper for PairFromToNat {
    type In = (u8, nat);

    type Out = nat;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        let curr = i.0;
        curr >= LEB128_CONT_BIT
    }

    open spec fn wf_out(&self, o: Self::Out) -> bool {
        o >= LEB128_CONT_BIT
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        let (lsb, rest) = i;
        128 * rest + (lsb - LEB128_CONT_BIT) as nat
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        let rest = o / 128;
        let lsb = (o % 128) as u8 | LEB128_CONT_BIT;
        (lsb, rest)
    }
}

pub type TerminalByteFmt = Mapped<Refined<U8, PredFnSpec<u8>>, U8FromToNat>;

pub type StepFmt<Rec> = Mapped<Refined<Pair<U8, Rec>, PredFnSpec<(u8, nat)>>, PairFromToNat>;

pub open spec fn terminal_byte_fmt() -> TerminalByteFmt {
    Mapped { inner: Refined(U8, |b: u8| b < LEB128_CONT_BIT), mapper: U8FromToNat }
}

pub open spec fn step_fmt(rec: BundledSpecs<nat>) -> StepFmt<BundledSpecs<nat>> {
    Mapped {
        inner: Refined(Pair(U8, rec), |x: (u8, nat)| x.0 >= LEB128_CONT_BIT),
        mapper: PairFromToNat,
    }
}

pub struct Leb128Body;

impl SpecRecBody for Leb128Body {
    type T = nat;

    type Body = Alt<TerminalByteFmt, StepFmt<BundledSpecs<nat>>>;

    open spec fn spec_body(rec: BundledSpecs<Self::T>) -> Self::Body {
        Alt(terminal_byte_fmt(), step_fmt(rec))
    }
}

pub type Leb128Fmt<const N: usize> = Fix<N, Leb128Body>;

pub open spec fn leb128_fmt<const N: usize>() -> Leb128Fmt<N> {
    Fix(Leb128Body)
}

pub struct Leb128<const N: usize>;

impl<const N: usize> SpecParser for Leb128<N> {
    type PVal = nat;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        leb128_fmt::<N>().spec_parse(ibuf)
    }
}

impl<const N: usize> Consistency for Leb128<N> {
    type Val = nat;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        leb128_fmt::<N>().consistent(v)
    }
}

impl<const N: usize> SpecSerializerDps for Leb128<N> {
    type SValue = nat;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        leb128_fmt::<N>().spec_serialize_dps(v, obuf)
    }
}

impl<const N: usize> SpecSerializer for Leb128<N> {
    type SVal = nat;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        leb128_fmt::<N>().spec_serialize(v)
    }
}

impl<const N: usize> SpecByteLen for Leb128<N> {
    type T = nat;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        leb128_fmt::<N>().byte_len(v)
    }
}

} // verus!
