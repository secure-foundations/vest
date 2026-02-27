use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A> SpecParser for super::Opt<A> where A: SpecParser {
    type PVal = Option<A::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n, v)) => Some((n, Some(v))),
            None => Some((0, None)),
        }
    }
}

impl<A> Consistency for super::Opt<A> where A: Consistency {
    type Val = Option<A::Val>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        match v {
            None => true,
            Some(vv) => self.0.consistent(vv),
        }
    }
}

impl<A> SoundParser for super::Opt<A> where A: SoundParser {
    open spec fn inv(&self) -> bool {
        self.0.inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        assert(self.inv());
        self.0.lemma_parse_safe(ibuf);
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        match self.0.spec_parse(ibuf) {
            Some((n, vv)) => {
                assert(self.inv());
                self.0.lemma_parse_sound_consumption(ibuf);
            },
            None => {},
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        assert(self.inv());
        self.0.lemma_parse_sound_value(ibuf);
    }
}

impl<A> SpecSerializerDps for super::Opt<A> where A: SpecSerializerDps {
    type ST = Option<A::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            None => obuf,
            Some(vv) => self.0.spec_serialize_dps(vv, obuf),
        }
    }
}

impl<A> SpecSerializer for super::Opt<A> where A: SpecSerializer {
    type SVal = Option<A::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match v {
            None => Seq::empty(),
            Some(vv) => self.0.spec_serialize(vv),
        }
    }
}

impl<A: Unambiguity> Unambiguity for super::Opt<A> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }
}

impl<A> NonTailFmt for super::Opt<A> where A: NonTailFmt {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            None => {
                assert(self.spec_serialize_dps(v, obuf) == Seq::empty() + obuf);
            },
            Some(vv) => {
                self.0.lemma_serialize_dps_prepend(vv, obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_dps_len(vv, obuf);
            },
        }
    }
}

impl<A: GoodSerializer> GoodSerializer for super::Opt<A> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match v {
            None => {},
            Some(vv) => {
                self.0.lemma_serialize_len(vv);
            },
        }
    }
}

impl<Inner: SpecByteLen> SpecByteLen for super::Opt<Inner> {
    type T = Option<Inner::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match v {
            None => 0,
            Some(vv) => self.0.byte_len(vv),
        }
    }
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Optional<A, B> {
    type PVal = (Option<A::PVal>, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (super::Opt(self.0), self.1).spec_parse(ibuf)
    }
}

impl<A, B> Consistency for super::Optional<A, B> where A: Consistency, B: Consistency {
    type Val = (Option<A::Val>, B::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (super::Opt(self.0), self.1).consistent(v)
    }
}

impl<A, B> SoundParser for super::Optional<A, B> where A: SoundParser, B: SoundParser {
    open spec fn inv(&self) -> bool {
        &&& self.0.inv()
        &&& self.1.inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_safe(ibuf)
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_parse_sound_value(ibuf)
    }
}

impl<A: SpecSerializerDps, B: SpecSerializerDps> SpecSerializerDps for super::Optional<A, B> {
    type ST = (Option<A::ST>, B::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (super::Opt(self.0), self.1).spec_serialize_dps(v, obuf)
    }
}

impl<A: NonTailFmt, B: NonTailFmt> NonTailFmt for super::Optional<A, B> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_dps_prepend(v, obuf)
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        (super::Opt(self.0), self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Optional<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        (super::Opt(self.0), self.1).lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Optional<A, B> {
    type T = (Option<A::T>, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (super::Opt(self.0), self.1).byte_len(v)
    }
}

impl<A: SpecSerializer, B: SpecSerializer> SpecSerializer for super::Optional<A, B> {
    type SVal = (Option<A::SVal>, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (super::Opt(self.0), self.1).spec_serialize(v)
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Optional<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

} // verus!
