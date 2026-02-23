use crate::combinators::length::AsLen;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::Varied;

verus! {

pub uninterp spec fn array_from_seq<const N: usize, T>(s: Seq<T>) -> [T; N]
    recommends
        s.len() == N,
;

pub broadcast axiom fn axiom_array_from_seq<const N: usize, T>(s: Seq<T>)
    requires
        s.len() == N,
    ensures
        (#[trigger] array_from_seq::<N, T>(s))@ == s,
;

impl<const N: usize> SpecParser for super::Fixed<N> {
    type PVal = [u8; N];

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() < N as int {
            None
        } else {
            Some((N as int, array_from_seq(ibuf.take(N as int))))
        }
    }
}

impl<const N: usize> Consistency for super::Fixed<N> {
    type Val = [u8; N];

    open spec fn consistent(&self, _v: Self::Val) -> bool {
        true
    }
}

impl<const N: usize> GoodParser for super::Fixed<N> {
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
    }
}

impl<const N: usize> SpecSerializerDps for super::Fixed<N> {
    type ST = [u8; N];

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v@ + obuf
    }
}

impl<const N: usize> SpecSerializer for super::Fixed<N> {
    type SVal = [u8; N];

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v@
    }
}

impl<const N: usize> Serializability for super::Fixed<N> {

}

impl<const N: usize> Unambiguity for super::Fixed<N> {

}

impl<const N: usize> GoodSerializerDps for super::Fixed<N> {
    proof fn lemma_serialize_dps_buf(&self, v: [u8; N], obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == v@ + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: [u8; N], obuf: Seq<u8>) {
    }
}

impl<const N: usize> GoodSerializer for super::Fixed<N> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
    }
}

impl<const N: usize> SpecByteLen for super::Fixed<N> {
    type T = [u8; N];

    open spec fn byte_len(&self, _v: Self::T) -> nat {
        N as nat
    }
}

impl<Len: AsLen> SpecParser for super::Varied<Len> {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() < self.0.as_usize() {
            None
        } else {
            Some((self.0.as_usize() as int, ibuf.take(self.0.as_usize() as int)))
        }
    }
}

impl<Len: AsLen> Consistency for super::Varied<Len> {
    type Val = Seq<u8>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        v.len() == self.0.as_usize()
    }
}

impl<Len: AsLen> GoodParser for super::Varied<Len> {
    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
    }
}

impl<Len: AsLen> SpecSerializerDps for super::Varied<Len> {
    type ST = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

impl<Len: AsLen> SpecSerializer for super::Varied<Len> {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v
    }
}

impl<Len: AsLen> Unambiguity for super::Varied<Len> {
    open spec fn unambiguous(&self) -> bool {
        true
    }
}

impl<Len: AsLen> GoodSerializerDps for super::Varied<Len> {
    proof fn lemma_serialize_dps_buf(&self, v: Seq<u8>, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == v + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Seq<u8>, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == v.len());
    }
}

impl<Len: AsLen> GoodSerializer for super::Varied<Len> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.spec_serialize(v).len() == v.len());
    }
}

impl<Len: AsLen> SpecByteLen for super::Varied<Len> {
    type T = Seq<u8>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        v.len()
    }
}

impl<Len: AsLen> BytesCombinator for super::Varied<Len> {
    proof fn lemma_byte_len_is_buf_len(&self, s: Seq<u8>) {
    }
}

impl<Inner: SpecParser, Len: AsLen> SpecParser for super::ExactLen<Inner, Len> {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        super::AndThen(super::Varied(self.0), self.1).spec_parse(ibuf)
    }
}

impl<Inner: Consistency + SpecByteLen<T = Inner::Val>, Len: AsLen> Consistency for super::ExactLen<
    Inner,
    Len,
> {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.1.consistent(v)
        &&& self.0.as_usize() == self.1.byte_len(v)
    }
}

impl<Inner: GoodParser, Len: AsLen> GoodParser for super::ExactLen<Inner, Len> {
    open spec fn inv(&self) -> bool {
        super::AndThen(super::Varied(self.0), self.1).inv()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        super::AndThen(super::Varied(self.0), self.1).lemma_parse_len_bound(ibuf);
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        super::AndThen(super::Varied(self.0), self.1).lemma_parse_byte_len(ibuf);
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        super::AndThen(super::Varied(self.0), self.1).lemma_parse_consistent(ibuf);
    }
}

impl<Inner: SpecSerializerDps, Len: AsLen> SpecSerializerDps for super::ExactLen<Inner, Len> {
    type ST = Inner::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        super::AndThen(super::Varied(self.0), self.1).spec_serialize_dps(v, obuf)
    }
}

impl<Inner: SpecSerializer, Len: AsLen> SpecSerializer for super::ExactLen<Inner, Len> {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        super::AndThen(super::Varied(self.0), self.1).spec_serialize(v)
    }
}

impl<Inner: Unambiguity, Len: AsLen> Unambiguity for super::ExactLen<Inner, Len> {
    open spec fn unambiguous(&self) -> bool {
        super::AndThen(super::Varied(self.0), self.1).unambiguous()
    }
}

impl<Inner, Len> GoodSerializerDps for super::ExactLen<Inner, Len> where
    Inner: GoodSerializer + EquivSerializers,
    Len: AsLen,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        super::AndThen(super::Varied(self.0), self.1).lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        super::AndThen(super::Varied(self.0), self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner: GoodSerializer, Len: AsLen> GoodSerializer for super::ExactLen<Inner, Len> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        super::AndThen(super::Varied(self.0), self.1).lemma_serialize_len(v);
    }
}

impl<Inner: SpecByteLen, Len: AsLen> SpecByteLen for super::ExactLen<Inner, Len> {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        super::AndThen(super::Varied(self.0), self.1).byte_len(v)
    }
}

impl<A, Then> SpecParser for super::AndThen<A, Then> where
    A: SpecParser<PVal = Seq<u8>>,
    Then: SpecParser,
 {
    type PVal = Then::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            None => None,
            Some((len_a, chunk)) => match self.1.spec_parse(chunk) {
                Some((len_b, v)) if len_a == len_b => Some((len_a, v)),
                _ => None,
            },
        }
    }
}

impl<A, Then> Consistency for super::AndThen<A, Then> where
    A: Consistency<Val = Seq<u8>> + SpecByteLen<T = Seq<u8>>,
    Then: Consistency + SpecByteLen<T = Then::Val>,
 {
    type Val = Then::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.1.consistent(v)
        &&& exists|chunk: Seq<u8>|
            self.0.consistent(chunk) && self.0.byte_len(chunk) == self.1.byte_len(v)
    }
}

impl<A, Then> GoodParser for super::AndThen<A, Then> where
    A: BytesCombinator + GoodParser,
    Then: GoodParser,
 {
    open spec fn inv(&self) -> bool {
        self.0.inv() && self.1.inv()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_len_bound(ibuf);
        match self.0.spec_parse(ibuf) {
            None => {},
            Some((len_a, chunk)) => match self.1.spec_parse(chunk) {
                Some((len_b, _)) if len_a == len_b => self.1.lemma_parse_len_bound(chunk),
                _ => {},
            },
        }
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        match self.0.spec_parse(ibuf) {
            None => {},
            Some((len_a, chunk)) => match self.1.spec_parse(chunk) {
                Some((len_b, v)) if len_a == len_b => {
                    self.1.lemma_parse_byte_len(chunk);
                    assert(self.byte_len(v) == self.1.byte_len(v));
                },
                _ => {},
            },
        }
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        match self.0.spec_parse(ibuf) {
            None => {},
            Some((len_a, chunk)) => match self.1.spec_parse(chunk) {
                Some((len_b, v)) if len_a == len_b => {
                    self.0.lemma_parse_consistent(ibuf);
                    self.0.lemma_parse_byte_len(ibuf);
                    self.1.lemma_parse_byte_len(chunk);
                    self.1.lemma_parse_consistent(chunk);
                    assert(self.0.consistent(chunk));
                },
                _ => {},
            },
        }
    }
}

impl<A, Then> SpecSerializerDps for super::AndThen<A, Then> where
    A: SpecSerializerDps<ST = Seq<u8>>,
    Then: SpecSerializerDps,
 {
    type ST = Then::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(self.1.spec_serialize_dps(v, seq![]), obuf)
    }
}

impl<A, Then> SpecSerializer for super::AndThen<A, Then> where
    A: SpecSerializer<SVal = Seq<u8>>,
    Then: SpecSerializer,
 {
    type SVal = Then::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let inner_bytes = self.1.spec_serialize(v);
        self.0.spec_serialize(inner_bytes)
    }
}

impl<A, Then> Unambiguity for super::AndThen<A, Then> where
    A: Unambiguity<PVal = Seq<u8>>,
    Then: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous() && self.1.unambiguous()
    }
}

impl<A, Then> GoodSerializerDps for super::AndThen<A, Then> where
    A: BytesCombinator + GoodSerializerDps,
    Then: GoodSerializer + EquivSerializers,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        self.0.lemma_serialize_dps_buf(self.1.spec_serialize_dps(v, seq![]), obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        self.1.lemma_serialize_equiv_on_empty(v);
        self.1.lemma_serialize_len(v);
        let inner_bytes = self.1.spec_serialize_dps(v, seq![]);
        self.0.lemma_serialize_dps_len(inner_bytes, obuf);
        self.0.lemma_byte_len_is_buf_len(inner_bytes);
    }
}

impl<A, Then> GoodSerializer for super::AndThen<A, Then> where
    A: BytesCombinator + GoodSerializer,
    Then: GoodSerializer,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let inner_bytes = self.1.spec_serialize(v);
        self.1.lemma_serialize_len(v);
        self.0.lemma_serialize_len(inner_bytes);
        self.0.lemma_byte_len_is_buf_len(inner_bytes);
    }
}

impl<A, Then: SpecByteLen> SpecByteLen for super::AndThen<A, Then> {
    type T = Then::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.1.byte_len(v)
    }
}

// pub open spec fn fill_array_rec<const N: usize>(base: [u8; N], s: Seq<u8>, i: nat) -> [u8; N]
//     recommends
//         s.len() == N,
//         i <= N,
//     decreases i,
// {
//     if i == 0 {
//         base
//     } else {
//         let idx = (i - 1) as int;
//         // base[idx] = s[idx];
//         fill_array_rec(spec_array_update(base, idx, s[idx]), s, idx as nat)
//     }
// }
// pub open spec fn array_from_seq<const N: usize>(s: Seq<u8>) -> [u8; N]
//     recommends s.len() == N
// {
//     let base = vstd::array::spec_array_fill_for_copy_type::<u8, N>(0);
//     fill_array_rec(base, s, N as nat)
// }
// proof fn lemma_fill_array_rec<const N: usize>(base: [u8; N], s: Seq<u8>, i: nat)
//     requires
//         s.len() == N,
//         i <= N,
//     ensures
//         ({
//             let res = fill_array_rec(base, s, i);
//             forall|k: int| #![auto] 0 <= k < i ==> res[k] == s[k]
//         }),
//         ({
//             let res = fill_array_rec(base, s, i);
//             forall|k: int| #![auto] i <= k < N ==> res[k] == base[k]
//         }),
//     decreases i,
// {
//     if i == 0 {
//     } else {
//         let idx = (i - 1) as int;
//         let new_base = spec_array_update(base, idx, s[idx]);
//         lemma_fill_array_rec(new_base, s, idx as nat);
//         let res = fill_array_rec(base, s, i);
//         // Help Verus with array length
//         // assert(res.len() == N);
//         // assert(0 <= idx < N);
//         assert(res[idx] == new_base[idx]);
//         assert(new_base[idx] == s[idx]);
//         assert(res[idx] == s[idx]);
//     }
// }
// proof fn lemma_array_from_seq<const N: usize>(s: Seq<u8>)
//     requires s.len() == N,
//     ensures
//         array_from_seq::<N>(s)@ == s,
// {
//     let base = spec_array_fill_for_copy_type::<u8, N>(0);
//     lemma_fill_array_rec(base, s, N as nat);
//     assert(array_from_seq::<N>(s)@ =~= s);
// }
} // verus!
