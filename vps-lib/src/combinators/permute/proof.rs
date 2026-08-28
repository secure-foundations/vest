use crate::combinators::choice::Alt;
use crate::combinators::tuple::Pair;
use crate::combinators::Mapped;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

// ============================================================================
// Permute2
// ============================================================================
impl<P1: SafeParser, P2: SafeParser> SafeParser for super::Permute2<P1, P2> {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, self.1),
            Mapped { inner: Pair(self.1, self.0), mapper: |i| super::swap2(i) },
        ).lemma_parse_safe(ibuf);
    }
}

impl<P1: Productive, P2: Productive> Productive for super::Permute2<P1, P2> {
    open spec fn productive_inv(&self) -> bool {
        &&& self.0.productive_inv()
        &&& self.1.productive_inv()
    }

    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, self.1),
            Mapped { inner: Pair(self.1, self.0), mapper: |i| super::swap2(i) },
        ).lemma_productive(ibuf);
    }
}

// `NoLookAhead` is deliberately not implemented.

impl<P1: SoundParser, P2: SoundParser> SoundParser for super::Permute2<P1, P2> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let canonical = Pair(self.0, self.1);
        let swapped = Pair(self.1, self.0);
        canonical.lemma_parse_sound_consumption(ibuf);
        swapped.lemma_parse_sound_consumption(ibuf);
        // Either the declared order matched, in which case the length claim is `Pair`'s, or the
        // swapped order matched and the two length sums agree by commutativity of `nat` addition.
        if canonical.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = swapped.spec_parse(ibuf) {
                assert(self.byte_len(super::swap2(iv)) == swapped.byte_len(iv));
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let canonical = Pair(self.0, self.1);
        let swapped = Pair(self.1, self.0);
        canonical.lemma_parse_sound_value(ibuf);
        swapped.lemma_parse_sound_value(ibuf);
        // Both branches establish the same conjunction of component consistencies, just reordered.
        if canonical.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = swapped.spec_parse(ibuf) {
                assert(self.consistent(super::swap2(iv)));
            }
        }
    }
}

impl<P1, P2> SPRoundTripDps for super::Permute2<P1, P2> where
    P1: SPRoundTripDps + NonTailFmt,
    P2: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& self.0.serialize_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        let canonical = Pair(self.0, self.1);
        canonical.theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<P1, P2> EquivSerializersGeneral for super::Permute2<P1, P2> where
    P1: EquivSerializersGeneral,
    P2: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_serialize_equiv(v, obuf);
    }
}

impl<P1, P2> EquivSerializers for super::Permute2<P1, P2> where
    P1: EquivSerializersGeneral,
    P2: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Pair(self.0, self.1).lemma_serialize_equiv_on_empty(v);
    }
}

// ============================================================================
// Permute3
// ============================================================================
impl<A: SafeParser, B: SafeParser, C: SafeParser> SafeParser for super::Permute3<A, B, C> {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
        &&& self.2.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute2(self.1, self.2)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute2(self.0, self.2)),
                    mapper: |i| super::swap3_1(i),
                },
                Mapped {
                    inner: Pair(self.2, super::Permute2(self.0, self.1)),
                    mapper: |i| super::swap3_2(i),
                },
            ),
        ).lemma_parse_safe(ibuf);
    }
}

impl<A: Productive, B: Productive, C: Productive> Productive for super::Permute3<A, B, C> {
    open spec fn productive_inv(&self) -> bool {
        &&& self.0.productive_inv()
        &&& self.1.productive_inv()
        &&& self.2.productive_inv()
    }

    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute2(self.1, self.2)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute2(self.0, self.2)),
                    mapper: |i| super::swap3_1(i),
                },
                Mapped {
                    inner: Pair(self.2, super::Permute2(self.0, self.1)),
                    mapper: |i| super::swap3_2(i),
                },
            ),
        ).lemma_productive(ibuf);
    }
}

impl<A: SoundParser, B: SoundParser, C: SoundParser> SoundParser for super::Permute3<A, B, C> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
        &&& self.2.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute2(self.1, self.2));
        let b1 = Pair(self.1, super::Permute2(self.0, self.2));
        let b2 = Pair(self.2, super::Permute2(self.0, self.1));
        b0.lemma_parse_sound_consumption(ibuf);
        b1.lemma_parse_sound_consumption(ibuf);
        b2.lemma_parse_sound_consumption(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.byte_len(super::swap3_1(iv)) == b1.byte_len(iv));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.byte_len(super::swap3_2(iv)) == b2.byte_len(iv));
                }
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute2(self.1, self.2));
        let b1 = Pair(self.1, super::Permute2(self.0, self.2));
        let b2 = Pair(self.2, super::Permute2(self.0, self.1));
        b0.lemma_parse_sound_value(ibuf);
        b1.lemma_parse_sound_value(ibuf);
        b2.lemma_parse_sound_value(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.consistent(super::swap3_1(iv)));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.consistent(super::swap3_2(iv)));
                }
            }
        }
    }
}

impl<A, B, C> SPRoundTripDps for super::Permute3<A, B, C> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps + NonTailFmt,
    C: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& self.2.unambiguous()
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        Pair(self.0, super::Permute2(self.1, self.2)).theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl<A, B, C> EquivSerializersGeneral for super::Permute3<A, B, C> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        Pair(self.0, super::Permute2(self.1, self.2)).lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, C> EquivSerializers for super::Permute3<A, B, C> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Pair(self.0, super::Permute2(self.1, self.2)).lemma_serialize_equiv_on_empty(v);
    }
}

// ============================================================================
// Permute4
// ============================================================================
impl<A: SafeParser, B: SafeParser, C: SafeParser, D: SafeParser> SafeParser for super::Permute4<
    A,
    B,
    C,
    D,
> {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
        &&& self.2.safe_inv()
        &&& self.3.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute3(self.1, self.2, self.3)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: |i| super::swap4_1(i),
                },
                Alt::<_, _, false>(
                    Mapped {
                        inner: Pair(self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: |i| super::swap4_2(i),
                    },
                    Mapped {
                        inner: Pair(self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: |i| super::swap4_3(i),
                    },
                ),
            ),
        ).lemma_parse_safe(ibuf);
    }
}

impl<A: Productive, B: Productive, C: Productive, D: Productive> Productive for super::Permute4<
    A,
    B,
    C,
    D,
> {
    open spec fn productive_inv(&self) -> bool {
        &&& self.0.productive_inv()
        &&& self.1.productive_inv()
        &&& self.2.productive_inv()
        &&& self.3.productive_inv()
    }

    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute3(self.1, self.2, self.3)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: |i| super::swap4_1(i),
                },
                Alt::<_, _, false>(
                    Mapped {
                        inner: Pair(self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: |i| super::swap4_2(i),
                    },
                    Mapped {
                        inner: Pair(self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: |i| super::swap4_3(i),
                    },
                ),
            ),
        ).lemma_productive(ibuf);
    }
}

impl<
    A: SoundParser,
    B: SoundParser,
    C: SoundParser,
    D: SoundParser,
> SoundParser for super::Permute4<A, B, C, D> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
        &&& self.2.sound_inv()
        &&& self.3.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute3(self.1, self.2, self.3));
        let b1 = Pair(self.1, super::Permute3(self.0, self.2, self.3));
        let b2 = Pair(self.2, super::Permute3(self.0, self.1, self.3));
        let b3 = Pair(self.3, super::Permute3(self.0, self.1, self.2));
        b0.lemma_parse_sound_consumption(ibuf);
        b1.lemma_parse_sound_consumption(ibuf);
        b2.lemma_parse_sound_consumption(ibuf);
        b3.lemma_parse_sound_consumption(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.byte_len(super::swap4_1(iv)) == b1.byte_len(iv));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.byte_len(super::swap4_2(iv)) == b2.byte_len(iv));
                }
                if b2.spec_parse(ibuf) is None {
                    if let Some((_n, iv)) = b3.spec_parse(ibuf) {
                        assert(self.byte_len(super::swap4_3(iv)) == b3.byte_len(iv));
                    }
                }
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute3(self.1, self.2, self.3));
        let b1 = Pair(self.1, super::Permute3(self.0, self.2, self.3));
        let b2 = Pair(self.2, super::Permute3(self.0, self.1, self.3));
        let b3 = Pair(self.3, super::Permute3(self.0, self.1, self.2));
        b0.lemma_parse_sound_value(ibuf);
        b1.lemma_parse_sound_value(ibuf);
        b2.lemma_parse_sound_value(ibuf);
        b3.lemma_parse_sound_value(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.consistent(super::swap4_1(iv)));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.consistent(super::swap4_2(iv)));
                }
                if b2.spec_parse(ibuf) is None {
                    if let Some((_n, iv)) = b3.spec_parse(ibuf) {
                        assert(self.consistent(super::swap4_3(iv)));
                    }
                }
            }
        }
    }
}

impl<A, B, C, D> SPRoundTripDps for super::Permute4<A, B, C, D> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps + NonTailFmt,
    C: SPRoundTripDps + NonTailFmt,
    D: SPRoundTripDps,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& self.2.unambiguous()
        &&& self.3.unambiguous()
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
        &&& self.2.serialize_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl<A, B, C, D> EquivSerializersGeneral for super::Permute4<A, B, C, D> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializersGeneral,
    D: EquivSerializersGeneral,
 {
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_general_inv()
        &&& self.3.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, C, D> EquivSerializers for super::Permute4<A, B, C, D> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializersGeneral,
    D: EquivSerializers,
 {
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_general_inv()
        &&& self.3.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).lemma_serialize_equiv_on_empty(v);
    }
}

// ============================================================================
// Permute5
// ============================================================================
impl<A: SafeParser, B: SafeParser, C: SafeParser, D: SafeParser, E: SafeParser> SafeParser for super::Permute5<
    A,
    B,
    C,
    D,
    E,
> {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
        &&& self.2.safe_inv()
        &&& self.3.safe_inv()
        &&& self.4.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute4(self.0, self.2, self.3, self.4)),
                    mapper: |i| super::swap5_1(i),
                },
                Alt::<_, _, false>(
                    Mapped {
                        inner: Pair(self.2, super::Permute4(self.0, self.1, self.3, self.4)),
                        mapper: |i| super::swap5_2(i),
                    },
                    Alt::<_, _, false>(
                        Mapped {
                            inner: Pair(self.3, super::Permute4(self.0, self.1, self.2, self.4)),
                            mapper: |i| super::swap5_3(i),
                        },
                        Mapped {
                            inner: Pair(self.4, super::Permute4(self.0, self.1, self.2, self.3)),
                            mapper: |i| super::swap5_4(i),
                        },
                    ),
                ),
            ),
        ).lemma_parse_safe(ibuf);
    }
}

impl<A: Productive, B: Productive, C: Productive, D: Productive, E: Productive> Productive for super::Permute5<
    A,
    B,
    C,
    D,
    E,
> {
    open spec fn productive_inv(&self) -> bool {
        &&& self.0.productive_inv()
        &&& self.1.productive_inv()
        &&& self.2.productive_inv()
        &&& self.3.productive_inv()
        &&& self.4.productive_inv()
    }

    proof fn lemma_productive(&self, ibuf: Seq<u8>) {
        Alt::<_, _, false>(
            Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4)),
            Alt::<_, _, false>(
                Mapped {
                    inner: Pair(self.1, super::Permute4(self.0, self.2, self.3, self.4)),
                    mapper: |i| super::swap5_1(i),
                },
                Alt::<_, _, false>(
                    Mapped {
                        inner: Pair(self.2, super::Permute4(self.0, self.1, self.3, self.4)),
                        mapper: |i| super::swap5_2(i),
                    },
                    Alt::<_, _, false>(
                        Mapped {
                            inner: Pair(self.3, super::Permute4(self.0, self.1, self.2, self.4)),
                            mapper: |i| super::swap5_3(i),
                        },
                        Mapped {
                            inner: Pair(self.4, super::Permute4(self.0, self.1, self.2, self.3)),
                            mapper: |i| super::swap5_4(i),
                        },
                    ),
                ),
            ),
        ).lemma_productive(ibuf);
    }
}

impl<
    A: SoundParser,
    B: SoundParser,
    C: SoundParser,
    D: SoundParser,
    E: SoundParser,
> SoundParser for super::Permute5<A, B, C, D, E> {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
        &&& self.2.sound_inv()
        &&& self.3.sound_inv()
        &&& self.4.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4));
        let b1 = Pair(self.1, super::Permute4(self.0, self.2, self.3, self.4));
        let b2 = Pair(self.2, super::Permute4(self.0, self.1, self.3, self.4));
        let b3 = Pair(self.3, super::Permute4(self.0, self.1, self.2, self.4));
        let b4 = Pair(self.4, super::Permute4(self.0, self.1, self.2, self.3));
        b0.lemma_parse_sound_consumption(ibuf);
        b1.lemma_parse_sound_consumption(ibuf);
        b2.lemma_parse_sound_consumption(ibuf);
        b3.lemma_parse_sound_consumption(ibuf);
        b4.lemma_parse_sound_consumption(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.byte_len(super::swap5_1(iv)) == b1.byte_len(iv));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.byte_len(super::swap5_2(iv)) == b2.byte_len(iv));
                }
                if b2.spec_parse(ibuf) is None {
                    if let Some((_n, iv)) = b3.spec_parse(ibuf) {
                        assert(self.byte_len(super::swap5_3(iv)) == b3.byte_len(iv));
                    }
                    if b3.spec_parse(ibuf) is None {
                        if let Some((_n, iv)) = b4.spec_parse(ibuf) {
                            assert(self.byte_len(super::swap5_4(iv)) == b4.byte_len(iv));
                        }
                    }
                }
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        let b0 = Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4));
        let b1 = Pair(self.1, super::Permute4(self.0, self.2, self.3, self.4));
        let b2 = Pair(self.2, super::Permute4(self.0, self.1, self.3, self.4));
        let b3 = Pair(self.3, super::Permute4(self.0, self.1, self.2, self.4));
        let b4 = Pair(self.4, super::Permute4(self.0, self.1, self.2, self.3));
        b0.lemma_parse_sound_value(ibuf);
        b1.lemma_parse_sound_value(ibuf);
        b2.lemma_parse_sound_value(ibuf);
        b3.lemma_parse_sound_value(ibuf);
        b4.lemma_parse_sound_value(ibuf);
        if b0.spec_parse(ibuf) is None {
            if let Some((_n, iv)) = b1.spec_parse(ibuf) {
                assert(self.consistent(super::swap5_1(iv)));
            }
            if b1.spec_parse(ibuf) is None {
                if let Some((_n, iv)) = b2.spec_parse(ibuf) {
                    assert(self.consistent(super::swap5_2(iv)));
                }
                if b2.spec_parse(ibuf) is None {
                    if let Some((_n, iv)) = b3.spec_parse(ibuf) {
                        assert(self.consistent(super::swap5_3(iv)));
                    }
                    if b3.spec_parse(ibuf) is None {
                        if let Some((_n, iv)) = b4.spec_parse(ibuf) {
                            assert(self.consistent(super::swap5_4(iv)));
                        }
                    }
                }
            }
        }
    }
}

impl<A, B, C, D, E> SPRoundTripDps for super::Permute5<A, B, C, D, E> where
    A: SPRoundTripDps + NonTailFmt,
    B: SPRoundTripDps + NonTailFmt,
    C: SPRoundTripDps + NonTailFmt,
    D: SPRoundTripDps + NonTailFmt,
    E: SPRoundTripDps,
{
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& self.2.unambiguous()
        &&& self.3.unambiguous()
        &&& self.4.unambiguous()
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
        &&& self.2.serialize_dps_inv()
        &&& self.3.serialize_dps_inv()
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4)).theorem_serialize_dps_parse_roundtrip(
            v,
            obuf,
        );
    }
}

impl<A, B, C, D, E> EquivSerializersGeneral for super::Permute5<A, B, C, D, E> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializersGeneral,
    D: EquivSerializersGeneral,
    E: EquivSerializersGeneral,
{
    open spec fn equiv_general_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_general_inv()
        &&& self.3.equiv_general_inv()
        &&& self.4.equiv_general_inv()
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4)).lemma_serialize_equiv(v, obuf);
    }
}

impl<A, B, C, D, E> EquivSerializers for super::Permute5<A, B, C, D, E> where
    A: EquivSerializersGeneral,
    B: EquivSerializersGeneral,
    C: EquivSerializersGeneral,
    D: EquivSerializersGeneral,
    E: EquivSerializers,
{
    open spec fn equiv_inv(&self) -> bool {
        &&& self.0.equiv_general_inv()
        &&& self.1.equiv_general_inv()
        &&& self.2.equiv_general_inv()
        &&& self.3.equiv_general_inv()
        &&& self.4.equiv_inv()
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        Pair(self.0, super::Permute4(self.1, self.2, self.3, self.4)).lemma_serialize_equiv_on_empty(v);
    }
}

} // verus!
