use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::DepPair<A, spec_fn(A::PVal) -> B> where
    A: SpecParser,
    B: SpecParser,
 {
    type PVal = (A::PVal, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, key)) => {
                let next = (self.1)(key);
                match next.spec_parse(ibuf.skip(n1)) {
                    Some((n2, val)) => Some((n1 + n2, (key, val))),
                    None => None,
                }
            },
            None => None,
        }
    }
}

impl<A, B> Consistency for super::DepPair<A, spec_fn(A::Val) -> B> where
    A: Consistency,
    B: Consistency,
 {
    type Val = (A::Val, B::Val);

    open spec fn consistent(&self, value: Self::Val) -> bool {
        let (key, val) = value;
        self.0.consistent(key) && (self.1)(key).consistent(val)
    }
}

impl<A, B> SoundParser for super::DepPair<A, spec_fn(A::PVal) -> B> where
    A: SoundParser,
    B: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& forall|key: A::PVal| #[trigger] (self.1)(key).sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let next = (self.1)(key);
            next.lemma_parse_safe(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let parsed_next = (self.1)(key);
            parsed_next.lemma_parse_sound_consumption(ibuf.skip(n1));
            parsed_next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((n2, val)) = parsed_next.spec_parse(ibuf.skip(n1)) {
                assert((self.1)(key).byte_len(val) == parsed_next.byte_len(val));
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let next = (self.1)(key);
            next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((_n2, val)) = next.spec_parse(ibuf.skip(n1)) {
                assert(self.consistent((key, val)));
            }
        }
    }
}

impl<A, B> SpecSerializerDps for super::DepPair<A, spec_fn(A::ST) -> B> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps + Consistency<Val = B::ST>,
 {
    type ST = (A::ST, B::ST);

    open spec fn spec_serialize_dps(&self, value: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let (key, val) = value;
        let next = (self.1)(key);
        self.0.spec_serialize_dps(key, next.spec_serialize_dps(val, obuf))
    }
}

impl<A, B> SpecSerializer for super::DepPair<A, spec_fn(A::SVal) -> B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer + Consistency<Val = B::SVal>,
 {
    type SVal = (A::SVal, B::SVal);

    open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
        let (key, val) = value;
        let next = (self.1)(key);
        self.0.spec_serialize(key) + next.spec_serialize(val)
    }
}

impl<A, B> Unambiguity for super::DepPair<A, spec_fn(A::PVal) -> B> where
    A: Unambiguity,
    B: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& forall|key: A::PVal| #[trigger] (self.1)(key).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::DepPair<A, spec_fn(A::ST) -> B> where
    A: NonTailFmt + Consistency<Val = A::ST>,
    B: NonTailFmt + Consistency<Val = B::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& forall|key: A::ST| #[trigger] (self.1)(key).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, value: Self::ST, obuf: Seq<u8>) {
        let (key, val) = value;
        let next = (self.1)(key);
        let next_buf = next.spec_serialize_dps(val, obuf);

        next.lemma_serialize_dps_prepend(val, obuf);
        self.0.lemma_serialize_dps_prepend(key, next_buf);

        let witness_next = choose|w: Seq<u8>| next.spec_serialize_dps(val, obuf) == w + obuf;
        let witness_prefix = choose|w: Seq<u8>|
            self.0.spec_serialize_dps(key, next_buf) == w + next_buf;
        assert(self.spec_serialize_dps(value, obuf) == witness_prefix + witness_next + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, value: Self::ST, obuf: Seq<u8>) {
        let (key, val) = value;
        let next = (self.1)(key);
        let next_buf = next.spec_serialize_dps(val, obuf);
        next.lemma_serialize_dps_len(val, obuf);
        self.0.lemma_serialize_dps_len(key, next_buf);
    }
}

impl<A, B> GoodSerializer for super::DepPair<A, spec_fn(A::SVal) -> B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& forall|key: A::SVal| #[trigger] (self.1)(key).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, value: Self::SVal) {
        let (key, val) = value;
        let next = (self.1)(key);
        self.0.lemma_serialize_len(key);
        next.lemma_serialize_len(val);
    }
}

impl<A, B> SpecByteLen for super::DepPair<A, spec_fn(A::T) -> B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen + Consistency<Val = B::T>,
 {
    type T = (A::T, B::T);

    open spec fn byte_len(&self, value: Self::T) -> nat {
        let (key, val) = value;
        let next = (self.1)(key);
        self.0.byte_len(key) + next.byte_len(val)
    }
}

impl<A, B, Infer> SpecParser for super::ImplicitAuto<A, spec_fn(A::PVal) -> B, Infer> where
    A: SpecParser,
    B: SpecParser,
 {
    type PVal = B::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, a)) => {
                let next = (self.1)(a);
                match next.spec_parse(ibuf.skip(n1)) {
                    Some((n2, v)) => Some((n1 + n2, v)),
                    None => None,
                }
            },
            None => None,
        }
    }
}

impl<A, B> Consistency for super::ImplicitAuto<
    A,
    spec_fn(A::Val) -> B,
    spec_fn(B::Val) -> A::Val,
> where A: Consistency, B: Consistency {
    type Val = B::Val;

    open spec fn consistent(&self, value: Self::Val) -> bool {
        let a = (self.2)(value);
        self.0.consistent(a) && (self.1)(a).consistent(value)
    }
}

impl<A, B> super::LosslessImplicitAuto<A, B> for super::ImplicitAuto<
    A,
    spec_fn(A::Val) -> B,
    spec_fn(B::Val) -> A::Val,
> where A: Consistency + AdmitsUniqueVal, B: Consistency {
    proof fn lemma_value_determines_key(
        fmt: &super::ImplicitAuto<A, spec_fn(A::Val) -> B, spec_fn(B::Val) -> A::Val>,
        k1: A::Val,
        k2: A::Val,
        value: B::Val,
    ) {
        fmt.0.lemma_unique_consistent_val(k1, k2);
    }
}

impl<A, B> SpecSerializerDps for super::ImplicitAuto<
    A,
    spec_fn(A::ST) -> B,
    spec_fn(B::ST) -> A::ST,
> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps + Consistency<Val = B::ST>,
 {
    type ST = B::ST;

    open spec fn spec_serialize_dps(&self, value: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let a = (self.2)(value);
        let next = (self.1)(a);
        self.0.spec_serialize_dps(a, next.spec_serialize_dps(value, obuf))
    }
}

impl<A, B> SpecSerializer for super::ImplicitAuto<
    A,
    spec_fn(A::SVal) -> B,
    spec_fn(B::SVal) -> A::SVal,
> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer + Consistency<Val = B::SVal>,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
        let a = (self.2)(value);
        let next = (self.1)(a);
        self.0.spec_serialize(a) + next.spec_serialize(value)
    }
}

impl<A, B, Infer> Unambiguity for super::ImplicitAuto<A, spec_fn(A::PVal) -> B, Infer> where
    A: Unambiguity,
    B: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& forall|a: A::PVal| #[trigger] (self.1)(a).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::ImplicitAuto<
    A,
    spec_fn(A::ST) -> B,
    spec_fn(B::ST) -> A::ST,
> where A: NonTailFmt + Consistency<Val = A::ST>, B: NonTailFmt + Consistency<Val = B::ST> {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& forall|a: A::ST| #[trigger] (self.1)(a).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, value: Self::ST, obuf: Seq<u8>) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        let next_buf = next.spec_serialize_dps(value, obuf);

        next.lemma_serialize_dps_prepend(value, obuf);
        self.0.lemma_serialize_dps_prepend(a, next_buf);

        let witness_next = choose|w: Seq<u8>| next.spec_serialize_dps(value, obuf) == w + obuf;
        let witness_prefix = choose|w: Seq<u8>|
            self.0.spec_serialize_dps(a, next_buf) == w + next_buf;
        assert(self.spec_serialize_dps(value, obuf) == witness_prefix + witness_next + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, value: Self::ST, obuf: Seq<u8>) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        let next_buf = next.spec_serialize_dps(value, obuf);
        next.lemma_serialize_dps_len(value, obuf);
        self.0.lemma_serialize_dps_len(a, next_buf);
    }
}

impl<A, B> GoodSerializer for super::ImplicitAuto<
    A,
    spec_fn(A::SVal) -> B,
    spec_fn(B::SVal) -> A::SVal,
> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& forall|a: A::SVal| #[trigger] (self.1)(a).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, value: Self::SVal) {
        let a = (self.2)(value);
        let next = (self.1)(a);
        self.0.lemma_serialize_len(a);
        next.lemma_serialize_len(value);
    }
}

impl<A, B> SpecByteLen for super::ImplicitAuto<A, spec_fn(A::T) -> B, spec_fn(B::T) -> A::T> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen + Consistency<Val = B::T>,
 {
    type T = B::T;

    open spec fn byte_len(&self, value: Self::T) -> nat {
        let a = (self.2)(value);
        let next = (self.1)(a);
        self.0.byte_len(a) + next.byte_len(value)
    }
}

} // verus!
