use crate::combinators::{mapped::spec::*, Mapped, Pair, Refined};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub open spec fn bits<Repr: SpecByteLen, Tuple, Nominal>(
    repr: Repr,
    unpack: spec_fn(Repr::T) -> Tuple,
    pack: spec_fn(Tuple) -> Repr::T,
    refinement: PredFnSpec<Tuple>,
    ctor: spec_fn(Tuple) -> Nominal,
    dtor: spec_fn(Nominal) -> Tuple,
) -> Mapped<
    Refined<Mapped<Repr, BiMapper<Repr::T, Tuple>>, PredFnSpec<Tuple>>,
    BiMapper<Tuple, Nominal>,
> {
    Mapped {
        inner: Refined(Mapped { inner: repr, mapper: BiMap(unpack, pack) }, refinement),
        mapper: BiMap(ctor, dtor),
    }
}

impl<Repr, Tuple, Nominal> SpecParser for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + SpecParser<PVal = Repr::T>,
 {
    type PVal = Nominal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.spec_parse(ibuf)
    }
}

impl<Repr, Tuple, Nominal> SpecSerializerDps for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + SpecSerializerDps<SValue = Repr::T>,
 {
    type SValue = Nominal;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.spec_serialize_dps(v, obuf)
    }
}

impl<Repr, Tuple, Nominal> SpecSerializer for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + SpecSerializer<SVal = Repr::T>,
 {
    type SVal = Nominal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.spec_serialize(v)
    }
}

impl<Repr, Tuple, Nominal> Consistency for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + Consistency<Val = Repr::T>,
 {
    type Val = Nominal;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        &&& fmt.consistent(v)
        &&& (self.consistent)(v)
    }
}

impl<Repr, Tuple, Nominal> SpecByteLen for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen,
 {
    type T = Nominal;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.byte_len(v)
    }
}

impl<Repr, Tuple, Nominal> SafeParser for super::Bits<Repr, Tuple, Nominal> where
    Repr: SpecByteLen + SafeParser<PVal = Repr::T>,
 {
    open spec fn safe_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_parse_safe(ibuf);
    }
}

impl<Repr, Tuple, Nominal> SoundParser for super::Bits<Repr, Tuple, Nominal> where
    Repr: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        // &&& forall|ibuf| #[trigger]
        //     fmt.spec_parse(ibuf) matches Some((_, v)) ==> (self.consistent)(v)
        // &&& self.repr.sound_inv()
        // &&& forall|packed: Repr::T| #[trigger]
        //     self.repr.consistent(packed) ==> (self.pack)((self.unpack)(packed)) == packed
        // &&& forall|t: Tuple| #[trigger]
        //     ((self.refinement)(t)) && self.repr.consistent((self.pack)(t)) ==> (self.dtor)(
        //         (self.ctor)(t),
        //     ) == t
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        &&& fmt.sound_inv()
        &&& forall|ibuf| #[trigger]
            fmt.spec_parse(ibuf) matches Some((_, v)) ==> (self.consistent)(v)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_parse_sound_value(ibuf);
    }
}

impl<Repr, Tuple, Nominal> NonTailFmt for super::Bits<Repr, Tuple, Nominal> where Repr: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Repr, Tuple, Nominal> GoodSerializer for super::Bits<Repr, Tuple, Nominal> where
    Repr: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_serialize_len(v);
    }
}

impl<Repr, Tuple, Nominal> MinMaxByteLen for super::Bits<Repr, Tuple, Nominal> where
    Repr: MinMaxByteLen,
 {
    open spec fn min(&self) -> nat {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.min()
    }

    open spec fn max(&self) -> nat {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.max()
    }

    proof fn lemma_min_max_byte_len(&self, v: Self::T) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_min_max_byte_len(v);
    }
}

impl<Repr, Tuple, Nominal> StaticByteLen for super::Bits<Repr, Tuple, Nominal> where
    Repr: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        Repr::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        let fmt = bits(self.repr, self.unpack, self.pack, self.refinement, self.ctor, self.dtor);
        fmt.lemma_static_len_matches_byte_len(v);
    }
}

} // verus!
