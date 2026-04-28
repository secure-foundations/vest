use super::spec::*;
use crate::combinators::Fixed;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SPRoundTripDps for super::Refined<A, Pred> where
    A: SPRoundTripDps,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        self.0.theorem_serialize_dps_parse_roundtrip(v, obuf)
    }
}

// impl<A: PSRoundTrip, Pred: SpecPred<A::PVal>> PSRoundTrip for super::Refined<A, Pred> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<A: NonMalleable, Pred: SpecPred<A::PVal>> NonMalleable for super::Refined<A, Pred> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<A: NoLookAhead, Pred: SpecPred<A::PVal>> NoLookAhead for super::Refined<A, Pred> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.0.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    assert(self.no_lookahead_inv());
                    self.0.lemma_no_lookahead(i1, i2);
                    assert(self.0.spec_parse(i2) == Some((n, v)));
                    assert(self.spec_parse(i2) == Some((n, v)));
                }
            }
        }
    }
}

impl<A, Pred> EquivSerializersGeneral for super::Refined<A, Pred> where
    A: EquivSerializersGeneral,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.lemma_serialize_equiv(v, obuf);
    }
}

impl<A, Pred> EquivSerializers for super::Refined<A, Pred> where
    A: EquivSerializers,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SValue) {
        self.0.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Inner: SPRoundTripDps> SPRoundTripDps for super::Const<Inner, Inner::PVal> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::SValue, obuf: Seq<u8>) {
        assert(v == self.1);
        self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

// impl<Inner: PSRoundTrip> PSRoundTrip for super::Const<Inner, Inner::PVal> {
//     proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
//         self.0.theorem_parse_serialize_roundtrip(ibuf);
//     }
// }
impl<Inner: NonMalleable> NonMalleable for super::Const<Inner, Inner::PVal> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Inner: NoLookAhead> NoLookAhead for super::Const<Inner, Inner::PVal> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.0.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.0.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<Inner> EquivSerializersGeneral for super::Const<Inner, Inner::SVal> where
    Inner: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.lemma_serialize_equiv(v, obuf);
    }
}

impl<Inner> EquivSerializers for super::Const<Inner, Inner::SVal> where Inner: EquivSerializers {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SValue) {
        self.0.lemma_serialize_equiv_on_empty(v);
    }
}

impl<const N: usize> SPRoundTripDps for super::Const<Fixed::<N>, [u8; N]> {
    open spec fn unambiguous(&self) -> bool {
        self.0.unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const N: usize> NonMalleable for super::Const<Fixed::<N>, [u8; N]> {
    open spec fn nonmal_inv(&self) -> bool {
        self.0.nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        self.0.lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const N: usize> NoLookAhead for super::Const<Fixed::<N>, [u8; N]> {
    open spec fn no_lookahead_inv(&self) -> bool {
        self.0.no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(i1) {
            if 0 <= n <= i2.len() {
                if i2.take(n) == i1.take(n) {
                    self.0.lemma_no_lookahead(i1, i2);
                }
            }
        }
    }
}

impl<const N: usize> EquivSerializersGeneral for super::Const<Fixed::<N>, [u8; N]> {
    open spec fn equiv_general_inv(&self) -> bool {
        self.0.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.0.lemma_serialize_equiv(v, obuf);
    }
}

impl<const N: usize> EquivSerializers for super::Const<Fixed::<N>, [u8; N]> {
    open spec fn equiv_inv(&self) -> bool {
        self.0.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SValue) {
        self.0.lemma_serialize_equiv_on_empty(v);
    }
}

impl<Tg, Of> SPRoundTripDps for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SPRoundTripDps + NonTailFmt,
    Tg::T: DeepView<V = Tg::T>,
    Of: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Tg, Of> NonMalleable for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SoundParser + NonMalleable,
    Tg::T: DeepView<V = Tg::T>,
    Of: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Tg, Of> NoLookAhead for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + NoLookAhead<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_no_lookahead(i1, i2);
    }
}

impl<Tg, Of> EquivSerializersGeneral for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + EquivSerializersGeneral<SVal = Tg::T, SValue = Tg::T> + Consistency<
        Val = Tg::T,
    >,
    Tg::T: DeepView<V = Tg::T>,
    Of: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_serialize_equiv(v, obuf);
    }
}

impl<Tg, Of> EquivSerializers for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + EquivSerializersGeneral<SVal = Tg::T, SValue = Tg::T> + Consistency<
        Val = Tg::T,
    >,
    Tg::T: DeepView<V = Tg::T>,
    Of: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SValue) {
        with_prefix_tag(self.0, self.1, self.2).lemma_serialize_equiv_on_empty(v);
    }
}

impl<Tg, Of> SPRoundTripDps for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SPRoundTripDps,
    Tg::T: DeepView<V = Tg::T>,
    Of: SPRoundTripDps + NonTailFmt,
 {
    open spec fn unambiguous(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).unambiguous()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<Tg, Of> NonMalleable for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SoundParser + NonMalleable,
    Tg::T: DeepView<V = Tg::T>,
    Of: SoundParser + NonMalleable,
 {
    open spec fn nonmal_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).nonmal_inv()
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<Tg, Of> NoLookAhead for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + NoLookAhead<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: NoLookAhead,
 {
    open spec fn no_lookahead_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).no_lookahead_inv()
    }

    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_no_lookahead(i1, i2);
    }
}

impl<Tg, Of> EquivSerializersGeneral for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + EquivSerializersGeneral<SVal = Tg::T, SValue = Tg::T> + Consistency<
        Val = Tg::T,
    >,
    Tg::T: DeepView<V = Tg::T>,
    Of: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_serialize_equiv(v, obuf);
    }
}

impl<Tg, Of> EquivSerializers for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + EquivSerializers<SVal = Tg::T, SValue = Tg::T> + Consistency<Val = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: EquivSerializersGeneral,
 {
    open spec fn equiv_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SValue) {
        with_suffix_tag(self.0, self.1, self.2).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
