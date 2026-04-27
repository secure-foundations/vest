use crate::combinators::{Fixed, Preceded2, Terminated2};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, Pred> SpecParser for super::Refined<A, Pred> where A: SpecParser, Pred: SpecPred<A::PVal> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if self.pred.apply(v) => Some((n, v)),
            _ => None,
        }
    }
}

impl<A, Pred> Consistency for super::Refined<A, Pred> where A: Consistency, Pred: SpecPred<A::Val> {
    type Val = A::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.inner.consistent(v) && self.pred.apply(v)
    }
}

impl<A, Pred> SafeParser for super::Refined<A, Pred> where A: SafeParser, Pred: SpecPred<A::PVal> {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<A, Pred> SoundParser for super::Refined<A, Pred> where
    A: SoundParser,
    Pred: SpecPred<A::PVal>,
 {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<A, Pred> SpecSerializerDps for super::Refined<A, Pred> where
    A: SpecSerializerDps,
    Pred: SpecPred<A::SValue>,
 {
    type SValue = A::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<A, Pred> SpecSerializer for super::Refined<A, Pred> where
    A: SpecSerializer,
    Pred: SpecPred<A::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<A, Pred> NonTailFmt for super::Refined<A, Pred> where
    A: NonTailFmt,
    Pred: SpecPred<A::SValue>,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, Pred> GoodSerializer for super::Refined<A, Pred> where
    A: GoodSerializer,
    Pred: SpecPred<A::SVal>,
 {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(v);
    }
}

impl<A, Pred> SpecByteLen for super::Refined<A, Pred> where A: SpecByteLen, Pred: SpecPred<A::T> {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v)
    }
}

impl<A, Pred> StaticByteLen for super::Refined<A, Pred> where
    A: StaticByteLen,
    Pred: SpecPred<A::T>,
 {
    open spec fn static_byte_len() -> nat {
        A::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len(v);
    }
}

impl<A, Pred> ValueByteLen for super::Refined<A, Pred> where A: ValueByteLen, Pred: SpecPred<A::T> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_value_len_matches_byte_len(v);
    }
}

impl<Inner> SpecParser for super::Tag<Inner, Inner::PVal> where Inner: SpecParser {
    type PVal = Inner::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag => Some((n, v)),
            _ => None,
        }
    }
}

impl<Inner> Consistency for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    type Val = Inner::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.inner.consistent(v)
        &&& v == self.tag
    }
}

impl<Inner> AdmitsUniqueVal for super::Tag<Inner, Inner::Val> where Inner: Consistency {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
        if self.consistent(v1) && self.consistent(v2) {
            assert(v1 == self.tag);
            assert(v2 == self.tag);
        }
    }
}

impl<Inner> SafeParser for super::Tag<Inner, Inner::PVal> where Inner: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<Inner> SoundParser for super::Tag<Inner, Inner::PVal> where Inner: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<Inner> SpecSerializerDps for super::Tag<Inner, Inner::SValue> where Inner: SpecSerializerDps {
    type SValue = Inner::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<Inner> SpecSerializer for super::Tag<Inner, Inner::SVal> where Inner: SpecSerializer {
    type SVal = Inner::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<Inner> NonTailFmt for super::Tag<Inner, Inner::SValue> where Inner: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<Inner> GoodSerializer for super::Tag<Inner, Inner::SVal> where Inner: GoodSerializer {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(v);
    }
}

impl<Inner> SpecByteLen for super::Tag<Inner, Inner::T> where Inner: SpecByteLen {
    type T = Inner::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v)
    }
}

impl<Inner> StaticByteLen for super::Tag<Inner, Inner::T> where Inner: StaticByteLen {
    open spec fn static_byte_len() -> nat {
        Inner::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len(v);
    }
}

impl<Inner> ValueByteLen for super::Tag<Inner, Inner::T> where Inner: ValueByteLen {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Inner::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_value_len_matches_byte_len(v);
    }
}

impl<const N: usize> SpecParser for super::Tag<Fixed::<N>, [u8; N]> {
    type PVal = Seq<u8>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.inner.spec_parse(ibuf) {
            Some((n, v)) if v == self.tag@ => Some((n, v)),
            _ => None,
        }
    }
}

impl<const N: usize> Consistency for super::Tag<Fixed::<N>, [u8; N]> {
    type Val = Seq<u8>;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        &&& self.inner.consistent(v)
        &&& v == self.tag@
    }
}

impl<const N: usize> AdmitsUniqueVal for super::Tag<Fixed::<N>, [u8; N]> {
    proof fn lemma_unique_consistent_val(&self, v1: Self::Val, v2: Self::Val) {
        if self.consistent(v1) && self.consistent(v2) {
            assert(v1 == self.tag@);
            assert(v2 == self.tag@);
        }
    }
}

impl<const N: usize> SafeParser for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn safe_inv(&self) -> bool {
        self.inner.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_safe(ibuf);
    }
}

impl<const N: usize> SoundParser for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn sound_inv(&self) -> bool {
        self.inner.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.inner.lemma_parse_sound_value(ibuf);
    }
}

impl<const N: usize> SpecSerializerDps for super::Tag<Fixed::<N>, [u8; N]> {
    type SValue = Seq<u8>;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.inner.spec_serialize_dps(v, obuf)
    }
}

impl<const N: usize> SpecSerializer for super::Tag<Fixed::<N>, [u8; N]> {
    type SVal = Seq<u8>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.inner.spec_serialize(v)
    }
}

impl<const N: usize> NonTailFmt for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn serialize_dps_inv(&self) -> bool {
        self.inner.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        self.inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<const N: usize> GoodSerializer for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn serialize_inv(&self) -> bool {
        self.inner.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        self.inner.lemma_serialize_len(v);
    }
}

impl<const N: usize> SpecByteLen for super::Tag<Fixed::<N>, [u8; N]> {
    type T = Seq<u8>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.inner.byte_len(v)
    }
}

impl<const N: usize> StaticByteLen for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn static_byte_len() -> nat {
        Fixed::<N>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_static_len_matches_byte_len(v);
    }
}

impl<const N: usize> ValueByteLen for super::Tag<Fixed::<N>, [u8; N]> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Fixed::<N>::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        self.inner.lemma_value_len_matches_byte_len(v);
    }
}

pub open spec fn with_prefix_tag<Tg: SpecByteLen, Of>(
    tag_inner: Tg,
    tag: Tg::T,
    of: Of,
) -> Preceded2<super::Tag<Tg, Tg::T>, Tg::T, Of, false> {
    Preceded2 { a: super::Tag { inner: tag_inner, tag }, b: of, a_val: tag }
}

pub open spec fn with_suffix_tag<Tg: SpecByteLen, Of>(
    tag_inner: Tg,
    tag: Tg::T,
    of: Of,
) -> Terminated2<Of, super::Tag<Tg, Tg::T>, Tg::T, false> {
    Terminated2 { a: of, b: super::Tag { inner: tag_inner, tag }, b_val: tag }
}

impl<Tg, Of> SpecParser for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SpecParser<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecParser,
 {
    type PVal = Of::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        with_prefix_tag(self.0, self.1, self.2).spec_parse(ibuf)
    }
}

impl<Tg, Of> Consistency for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + Consistency<Val = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: Consistency,
 {
    type Val = Of::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        with_prefix_tag(self.0, self.1, self.2).consistent(v)
    }
}

impl<Tg, Of> SafeParser for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SafeParser<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_parse_safe(ibuf)
    }
}

impl<Tg, Of> SoundParser for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SoundParser,
    Tg::T: DeepView<V = Tg::T>,
    Of: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_parse_sound_value(ibuf)
    }
}

impl<Tg, Of> SpecSerializerDps for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SpecSerializerDps<SValue = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecSerializerDps,
 {
    type SValue = Of::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        with_prefix_tag(self.0, self.1, self.2).spec_serialize_dps(v, obuf)
    }
}

impl<Tg, Of> SpecSerializer for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + SpecSerializer<SVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecSerializer,
 {
    type SVal = Of::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        with_prefix_tag(self.0, self.1, self.2).spec_serialize(v)
    }
}

impl<Tg, Of> NonTailFmt for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + NonTailFmt,
    Tg::T: DeepView<V = Tg::T>,
    Of: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_prefix_tag(self.0, self.1, self.2).lemma_serialize_dps_len(v, obuf);
    }
}

impl<Tg, Of> GoodSerializer for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen + GoodSerializer,
    Tg::T: DeepView<V = Tg::T>,
    Of: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        with_prefix_tag(self.0, self.1, self.2).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        with_prefix_tag(self.0, self.1, self.2).lemma_serialize_len(v);
    }
}

impl<Tg, Of> SpecByteLen for super::WithPrefixTag<Tg, Of> where
    Tg: SpecByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecByteLen,
 {
    type T = Of::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        with_prefix_tag(self.0, self.1, self.2).byte_len(v)
    }
}

impl<Tg, Of> StaticByteLen for super::WithPrefixTag<Tg, Of> where
    Tg: StaticByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        Tg::static_byte_len() + Of::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        with_prefix_tag(self.0, self.1, self.2).lemma_static_len_matches_byte_len(v);
    }
}

impl<Tg, Of> ValueByteLen for super::WithPrefixTag<Tg, Of> where
    Tg: StaticByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: ValueByteLen,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Tg::static_byte_len() + Of::value_byte_len(v)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        with_prefix_tag(self.0, self.1, self.2).lemma_value_len_matches_byte_len(v);
    }
}

impl<Tg, Of> SpecParser for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SpecParser<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecParser,
 {
    type PVal = Of::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        with_suffix_tag(self.0, self.1, self.2).spec_parse(ibuf)
    }
}

impl<Tg, Of> Consistency for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + Consistency<Val = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: Consistency,
 {
    type Val = Of::Val;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        with_suffix_tag(self.0, self.1, self.2).consistent(v)
    }
}

impl<Tg, Of> SafeParser for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SafeParser<PVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_parse_safe(ibuf)
    }
}

impl<Tg, Of> SoundParser for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SoundParser,
    Tg::T: DeepView<V = Tg::T>,
    Of: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_parse_sound_consumption(ibuf)
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_parse_sound_value(ibuf)
    }
}

impl<Tg, Of> SpecSerializerDps for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SpecSerializerDps<SValue = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecSerializerDps,
 {
    type SValue = Of::SValue;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        with_suffix_tag(self.0, self.1, self.2).spec_serialize_dps(v, obuf)
    }
}

impl<Tg, Of> SpecSerializer for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + SpecSerializer<SVal = Tg::T>,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecSerializer,
 {
    type SVal = Of::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        with_suffix_tag(self.0, self.1, self.2).spec_serialize(v)
    }
}

impl<Tg, Of> NonTailFmt for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + NonTailFmt,
    Tg::T: DeepView<V = Tg::T>,
    Of: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        with_suffix_tag(self.0, self.1, self.2).lemma_serialize_dps_len(v, obuf);
    }
}

impl<Tg, Of> GoodSerializer for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen + GoodSerializer,
    Tg::T: DeepView<V = Tg::T>,
    Of: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        with_suffix_tag(self.0, self.1, self.2).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        with_suffix_tag(self.0, self.1, self.2).lemma_serialize_len(v);
    }
}

impl<Tg, Of> SpecByteLen for super::WithSuffixTag<Tg, Of> where
    Tg: SpecByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: SpecByteLen,
 {
    type T = Of::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        with_suffix_tag(self.0, self.1, self.2).byte_len(v)
    }
}

impl<Tg, Of> StaticByteLen for super::WithSuffixTag<Tg, Of> where
    Tg: StaticByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        Of::static_byte_len() + Tg::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        with_suffix_tag(self.0, self.1, self.2).lemma_static_len_matches_byte_len(v);
    }
}

impl<Tg, Of> ValueByteLen for super::WithSuffixTag<Tg, Of> where
    Tg: StaticByteLen,
    Tg::T: DeepView<V = Tg::T>,
    Of: ValueByteLen,
 {
    open spec fn value_byte_len(v: Self::T) -> nat {
        Of::value_byte_len(v) + Tg::static_byte_len()
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        with_suffix_tag(self.0, self.1, self.2).lemma_value_len_matches_byte_len(v);
    }
}

} // verus!
