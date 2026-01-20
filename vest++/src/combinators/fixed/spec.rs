use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub uninterp spec fn array_from_seq<const N: usize>(s: Seq<u8>) -> [u8; N]
    recommends
        s.len() == N,
;

pub broadcast axiom fn axiom_array_from_seq<const N: usize>(s: Seq<u8>)
    requires
        s.len() == N,
    ensures
        (#[trigger] array_from_seq::<N>(s))@ == s,
;

impl<const N: usize> SpecParser for super::Fixed<N> {
    type PVal = [u8; N];

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() < N as int {
            None
        } else {
            Some((N as int, array_from_seq::<N>(ibuf.take(N as int))))
        }
    }
}

impl<const N: usize> GoodParser for super::Fixed<N> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        assert forall|i: int| 0 <= i < N implies #[trigger] ibuf[i].wf() by {}
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
        if v.wf() {
            assert(self.spec_serialize_dps(v, obuf) == v@ + obuf);
        }
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
