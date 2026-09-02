//! Correctness proofs for byte-aligned bitfield formats.
use crate::combinators::{mapped::spec::*, Mapped, Pair, Refined};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::spec::*;

verus! {

impl<Repr, Tuple, Nominal> SPRoundTripDps for super::Bits<Repr, Tuple, Nominal> where
    Repr: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        // let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        // fmt.unambiguous()
        // &&& forall|ibuf| #[trigger]
        //     fmt.spec_parse(ibuf) matches Some((_, v)) ==> (self.consistent)(v)
        &&& self.repr.unambiguous()
        &&& forall|unpacked: Tuple|
            (#[trigger] (self.consistent)((self.ctor)(unpacked)) && (self.refinement)(unpacked))
                ==> (self.unpack)((self.pack)(unpacked)) == unpacked
        &&& forall|t: Nominal| #[trigger] (self.consistent)(t) ==> (self.ctor)((self.dtor)(t)) == t
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let packed = (self.pack)((self.dtor)(v));
        self.repr.theorem_serialize_dps_parse_roundtrip(packed, obuf);
    }
}

impl<Repr, Tuple, Nominal> NonMalleable for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + SoundParser + NonMalleable<PVal = Repr::T>,
 {
    open spec fn nonmal_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Repr, Tuple, Nominal> NoLookAhead for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + NoLookAhead<PVal = Repr::T>,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        assert(self.no_lookahead_inv() == fmt.no_lookahead_inv());
        fmt.lemma_no_lookahead(i1, i2);
    }
}

impl<Repr, Tuple, Nominal> Productive for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + Productive<PVal = Repr::T>,
 {
    open spec fn productive_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.productive_inv()
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_productive(s);
    }
}

impl<Repr, Tuple, Nominal> EquivSerializersGeneral for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + EquivSerializersGeneral<SVal = Repr::T>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_serialize_equiv(v, obuf);
    }
}

impl<Repr, Tuple, Nominal> EquivSerializers for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + EquivSerializers<SVal = Repr::T>,
 {
    open spec fn equiv_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
