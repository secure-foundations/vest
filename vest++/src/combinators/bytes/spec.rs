use crate::core::{proof::*, spec::*};
use vstd::calc;
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

pub proof fn lemma_seq_u8_blen_is_len(v: Seq<u8>)
    ensures
        v.blen() == v.len(),
    decreases v.len(),
{
    let f = |acc: nat, elem: u8| acc + elem.blen();

    if v.len() == 0 {
    } else {
        let first = v[0];
        let rest = v.skip(1);

        lemma_seq_u8_blen_is_len(rest);

        calc! {
            (==)
            v.fold_left(0, f); {
                v.lemma_fold_left_alt(0, f);
            }
            v.fold_left_alt(0, f); {}
            rest.fold_left_alt(f(0, first), f); {}
            rest.fold_left_alt(first.blen(), f); {
                assert(first.blen() == 1);
                rest.lemma_fold_left_alt(first.blen(), f);
            }
            rest.fold_left(first.blen(), f); {
                super::super::star::proof::lemma_fold_left_accumulate_nat(rest, first.blen(), f);
            }
            first.blen() + rest.fold_left(0, f);
        }
    }
}

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

impl SpecParser for super::Varied {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if ibuf.len() < self.0 {
            None
        } else {
            Some((self.0 as int, ibuf.take(self.0 as int)))
        }
    }
}

impl GoodParser for super::Varied {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
    }
}

impl SpecSerializerDps for super::Varied {
    type ST = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        v + obuf
    }
}

impl SpecSerializer for super::Varied {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        v
    }
}

impl Unambiguity for super::Varied {
    open spec fn unambiguous(&self) -> bool {
        forall|b: Self::PVal| b.len() == self.0
    }
}

impl GoodSerializerDps for super::Varied {
    proof fn lemma_serialize_dps_buf(&self, v: Seq<u8>, obuf: Seq<u8>) {
        if v.wf() {
            assert(self.spec_serialize_dps(v, obuf) == v + obuf);
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Seq<u8>, obuf: Seq<u8>) {
        lemma_seq_u8_blen_is_len(v);
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == v.len());
        assert(self.byte_len(v) == v.blen());
    }
}

impl GoodSerializer for super::Varied {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        lemma_seq_u8_blen_is_len(v);
        assert(self.spec_serialize(v).len() == v.len());
        assert(self.byte_len(v) == v.blen());
    }
}

impl SpecByteLen for super::Varied {
    type T = Seq<u8>;
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
