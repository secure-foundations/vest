use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Implicit<A, spec_fn(A::PVal) -> B> where
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

impl<A, B> Consistency for super::Implicit<A, spec_fn(A::Val) -> B> where
    A: Consistency,
    B: Consistency,
 {
    type Val = B::Val;

    open spec fn consistent(&self, value: Self::Val) -> bool {
        exists|a: A::Val| #[trigger] self.0.consistent(a) && (self.1)(a).consistent(value)
    }
}

impl<A, B> super::LosslessImplicit<A, B> for super::Implicit<A, spec_fn(A::Val) -> B> where
    A: Consistency + AdmitsUniqueVal,
    B: Consistency,
 {
    proof fn lemma_value_uniquely_determines_key(
        fmt: &super::Implicit<A, spec_fn(A::Val) -> B>,
        k1: A::Val,
        k2: A::Val,
        value: B::Val,
    ) {
        fmt.0.lemma_unique_consistent_val(k1, k2);
    }
}

impl<A, B> SoundParser for super::Implicit<A, spec_fn(A::PVal) -> B> where
    A: SoundParser,
    B: SoundParser,
    Self: super::LosslessImplicit<A, B>,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& forall|a: A::PVal| #[trigger] (self.1)(a).sound_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
        if let Some((n1, a)) = self.0.spec_parse(ibuf) {
            let next = (self.1)(a);
            next.lemma_parse_safe(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, a_parsed)) = self.0.spec_parse(ibuf) {
            let parsed_next = (self.1)(a_parsed);
            parsed_next.lemma_parse_sound_consumption(ibuf.skip(n1));
            parsed_next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((n2, v)) = parsed_next.spec_parse(ibuf.skip(n1)) {
                let a = choose|a: A::T| self.0.consistent(a) && (self.1)(a).consistent(v);
                <Self as super::LosslessImplicit<A, B>>::lemma_value_uniquely_determines_key(
                    self,
                    a,
                    a_parsed,
                    v,
                );
                assert((self.1)(a).byte_len(v) == parsed_next.byte_len(v));
                assert(self.byte_len(v) == self.0.byte_len(a) + (self.1)(a).byte_len(v));
                assert(n1 + n2 == self.byte_len(v));
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, a)) = self.0.spec_parse(ibuf) {
            let next = (self.1)(a);
            next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((_n2, v)) = next.spec_parse(ibuf.skip(n1)) {
                assert(self.consistent(v));
            }
        }
    }
}

impl<A, B> SpecSerializerDps for super::Implicit<A, spec_fn(A::ST) -> B> where
    A: SpecSerializerDps + Consistency<Val = A::ST>,
    B: SpecSerializerDps + Consistency<Val = B::ST>,
 {
    type ST = B::ST;

    open spec fn spec_serialize_dps(&self, value: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let a = choose|a: A::ST| self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        self.0.spec_serialize_dps(a, next.spec_serialize_dps(value, obuf))
    }
}

impl<A, B> SpecSerializer for super::Implicit<A, spec_fn(A::SVal) -> B> where
    A: SpecSerializer + Consistency<Val = A::SVal>,
    B: SpecSerializer + Consistency<Val = B::SVal>,
 {
    type SVal = B::SVal;

    open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
        let a = choose|a: A::SVal| self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        self.0.spec_serialize(a) + next.spec_serialize(value)
    }
}

impl<A, B> Unambiguity for super::Implicit<A, spec_fn(A::PVal) -> B> where
    A: Unambiguity,
    B: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& forall|a: A::PVal| #[trigger] (self.1)(a).unambiguous()
    }
}

impl<A, B> NonTailFmt for super::Implicit<A, spec_fn(A::ST) -> B> where
    A: NonTailFmt + Consistency<Val = A::ST>,
    B: NonTailFmt + Consistency<Val = B::ST>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& forall|a: A::ST| #[trigger] (self.1)(a).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, value: Self::ST, obuf: Seq<u8>) {
        let a = choose|a: A::ST| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
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
        let a = choose|a: A::ST| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        let next_buf = next.spec_serialize_dps(value, obuf);
        next.lemma_serialize_dps_len(value, obuf);
        self.0.lemma_serialize_dps_len(a, next_buf);
    }
}

impl<A, B> GoodSerializer for super::Implicit<A, spec_fn(A::SVal) -> B> where
    A: GoodSerializer + Consistency<Val = A::SVal>,
    B: GoodSerializer + Consistency<Val = B::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& forall|a: A::SVal| #[trigger] (self.1)(a).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, value: Self::SVal) {
        let a = choose|a: A::SVal| #![auto] self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        self.0.lemma_serialize_len(a);
        next.lemma_serialize_len(value);
    }
}

impl<A, B> SpecByteLen for super::Implicit<A, spec_fn(A::T) -> B> where
    A: SpecByteLen + Consistency<Val = A::T>,
    B: SpecByteLen + Consistency<Val = B::T>,
 {
    type T = B::T;

    open spec fn byte_len(&self, value: Self::T) -> nat {
        let a = choose|a: A::T| self.0.consistent(a) && (self.1)(a).consistent(value);
        let next = (self.1)(a);
        self.0.byte_len(a) + next.byte_len(value)
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
