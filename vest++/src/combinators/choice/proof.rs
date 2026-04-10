use crate::combinators::choice::spec::{tag_position, unique_branch_match};
use crate::combinators::Sum;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A: SPRoundTripDps, B: SPRoundTripDps> SPRoundTripDps for super::Choice<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.theorem_serialize_dps_parse_roundtrip(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.theorem_serialize_dps_parse_roundtrip(vb, obuf);
            },
        }
    }
}

// impl<A: PSRoundTrip, B: PSRoundTrip> PSRoundTrip for super::Choice<A, B> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(ibuf);
//         self.1.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<A: NonMalleable, B: NonMalleable> NonMalleable for super::Choice<A, B> {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
        self.1.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, B: NoLookAhead> NoLookAhead for super::Choice<A, B> {
    open spec fn no_lookahead_inv(&self) -> bool {
        &&& self.0.no_lookahead_inv()
        &&& self.1.no_lookahead_inv()
        &&& disjoint_domains(self.0, self.1)
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        self.0.lemma_no_lookahead(i1, i2);
        self.1.lemma_no_lookahead(i1, i2);
        assert(disjoint_domains(self.0, self.1));
    }
}

impl<A, B> EquivSerializersGeneral for super::Choice<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_equiv(va, obuf);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_equiv(vb, obuf);
            },
        }
    }
}

impl<A, B> EquivSerializers for super::Choice<A, B> where A: EquivSerializers, B: EquivSerializers {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_inv()
        &&& self.1.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        match v {
            Sum::Inl(va) => {
                self.0.lemma_serialize_equiv_on_empty(va);
            },
            Sum::Inr(vb) => {
                self.1.lemma_serialize_equiv_on_empty(vb);
            },
        }
    }
}

impl<A: SPRoundTripDps, B: SPRoundTripDps<T = A::T>> SPRoundTripDps for super::Alt<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        if self.choose_left(v) {
            self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
        } else {
            self.1.theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }
}

// NonMalleable only holds for [`Alt`] when the two parsers produce disjoint sets of values.
// This ensures that if two byte sequences parse to the same value, they must have used the same underlying parser.
impl<A, B> NonMalleable for super::Alt<A, B> where
    A: SoundParser + NonMalleable,
    B: SoundParser<T = A::T> + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
        &&& self.0.nonmal_inv()
        &&& self.1.nonmal_inv()
        &&& disjoint_values(self.0, self.1)
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    let a_parses_buf1 = self.0.spec_parse(buf1) is Some;
                    let a_parses_buf2 = self.0.spec_parse(buf2) is Some;
                    if a_parses_buf1 && a_parses_buf2 {
                        // Both use parser A
                        self.0.lemma_parse_non_malleable(buf1, buf2);
                    } else if !a_parses_buf1 && !a_parses_buf2 {
                        // Both use parser B
                        self.1.lemma_parse_non_malleable(buf1, buf2);
                    } else {
                        // buf1 uses A; buf2 uses B
                        if a_parses_buf1 && !a_parses_buf2 {
                            self.0.lemma_parse_sound_value(buf1);
                            self.1.lemma_parse_sound_value(buf2);
                            assert(self.0.consistent(v1));
                            assert(self.1.consistent(v2));
                            assert(disjoint_values(self.0, self.1));
                        } else {
                            // buf1 uses B; buf2 uses A
                            self.1.lemma_parse_sound_value(buf1);
                            self.0.lemma_parse_sound_value(buf2);
                            assert(self.1.consistent(v1));
                            assert(self.0.consistent(v2));
                            assert(disjoint_values(self.0, self.1));
                        }
                    }
                }
            }
        }
    }
}

impl<A, B> NoLookAhead for super::Alt<A, B> where A: NoLookAhead, B: NoLookAhead<PVal = A::PVal> {
    open spec fn no_lookahead_inv(&self) -> bool {
        &&& self.0.no_lookahead_inv()
        &&& self.1.no_lookahead_inv()
        &&& disjoint_domains(self.0, self.1)
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        assert(self.no_lookahead_inv());
        self.0.lemma_no_lookahead(i1, i2);
        self.1.lemma_no_lookahead(i1, i2);
        assert(disjoint_domains(self.0, self.1));
    }
}

impl<A, B> EquivSerializersGeneral for super::Alt<A, B> where
    A: EquivSerializersGeneral + Consistency<Val = A::SVal>,
    B: EquivSerializersGeneral<SVal = A::SVal> + Consistency<Val = B::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        if self.choose_left(v) {
            self.0.lemma_serialize_equiv(v, obuf);
        } else {
            self.1.lemma_serialize_equiv(v, obuf);
        }
    }
}

impl<A, B> EquivSerializers for super::Alt<A, B> where
    A: EquivSerializers + Consistency<Val = A::SVal>,
    B: EquivSerializers<SVal = A::SVal> + Consistency<Val = B::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_inv()
        &&& self.1.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        if self.choose_left(v) {
            self.0.lemma_serialize_equiv_on_empty(v);
        } else {
            self.1.lemma_serialize_equiv_on_empty(v);
        }
    }
}

impl<T, C, const N: usize> SPRoundTripDps for super::Dispatch<T, C, N> where C: SPRoundTripDps {
    open spec fn unambiguous(&self) -> bool {
        self.active_branch().unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.active_branch().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<T, C: NonMalleable, const N: usize> NonMalleable for super::Dispatch<T, C, N> {
    open spec fn nonmal_inv(&self) -> bool {
        self.active_branch().nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((_n1, _v1)) = self.spec_parse(buf1) {
            if let Some((_n2, _v2)) = self.spec_parse(buf2) {
                self.active_branch().lemma_parse_non_malleable(buf1, buf2);
            }
        }
    }
}

impl<T, C: NoLookAhead, const N: usize> NoLookAhead for super::Dispatch<T, C, N> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.active_branch().no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.active_branch().lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<T, C, const N: usize> EquivSerializersGeneral for super::Dispatch<T, C, N> where
    C: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.active_branch().equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        self.active_branch().lemma_serialize_equiv(v, obuf);
    }
}

impl<T, C: EquivSerializers, const N: usize> EquivSerializers for super::Dispatch<T, C, N> {
    open spec fn equiv_inv(&self) -> bool {
        self.active_branch().equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        self.active_branch().lemma_serialize_equiv_on_empty(v);
    }
}

impl<A: SPRoundTripDps, B: SPRoundTripDps> SPRoundTripDps for Sum<A, B> {
    open spec fn unambiguous(&self) -> bool {
        match self {
            Sum::Inl(a) => a.unambiguous(),
            Sum::Inr(b) => b.unambiguous(),
        }
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.theorem_serialize_dps_parse_roundtrip(va, obuf),
            (Sum::Inr(b), Sum::Inr(vb)) => b.theorem_serialize_dps_parse_roundtrip(vb, obuf),
            _ => (),
        }
    }
}

impl<A: NonMalleable, B: NonMalleable> NonMalleable for Sum<A, B> {
    open spec fn nonmal_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.nonmal_inv(),
            Sum::Inr(b) => b.nonmal_inv(),
        }
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        match self {
            Sum::Inl(a) => a.lemma_parse_non_malleable(buf1, buf2),
            Sum::Inr(b) => b.lemma_parse_non_malleable(buf1, buf2),
        }
    }
}

impl<A: NoLookAhead, B: NoLookAhead> NoLookAhead for Sum<A, B> {
    open spec fn no_lookahead_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.no_lookahead_inv(),
            Sum::Inr(b) => b.no_lookahead_inv(),
        }
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        match self {
            Sum::Inl(a) => a.lemma_no_lookahead(i1, i2),
            Sum::Inr(b) => b.lemma_no_lookahead(i1, i2),
        }
    }
}

impl<A, B> EquivSerializersGeneral for Sum<A, B> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.equiv_general_inv(),
            Sum::Inr(b) => b.equiv_general_inv(),
        }
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.lemma_serialize_equiv(va, obuf),
            (Sum::Inr(b), Sum::Inr(vb)) => b.lemma_serialize_equiv(vb, obuf),
            _ => (),
        }
    }
}

impl<A, B> EquivSerializers for Sum<A, B> where A: EquivSerializers, B: EquivSerializers {
    open spec fn equiv_inv(&self) -> bool {
        match self {
            Sum::Inl(a) => a.equiv_inv(),
            Sum::Inr(b) => b.equiv_inv(),
        }
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        match (self, v) {
            (Sum::Inl(a), Sum::Inl(va)) => a.lemma_serialize_equiv_on_empty(va),
            (Sum::Inr(b), Sum::Inr(vb)) => b.lemma_serialize_equiv_on_empty(vb),
            _ => (),
        }
    }
}

} // verus!
