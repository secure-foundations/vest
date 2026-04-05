use crate::combinators::choice::Alt;
use crate::combinators::tuple::Pair;
use crate::combinators::Mapped;
use crate::core::{proof::*, spec::*};
use core::marker::PhantomData;
use vstd::prelude::*;

use super::{Swap2Mapper, Swap3Mapper1, Swap3Mapper2, Swap4Mapper1, Swap4Mapper2, Swap4Mapper3};

verus! {

// ============== Permute2 ==============
// Permute2 ::= Alt((P1, P2), Mapped((P2, P1), swap))
impl<P1, P2> SpecParser for super::Permute2<P1, P2> where P1: SpecParser, P2: SpecParser {
    type PVal = (P1::PVal, P2::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let inner = Alt(
            Pair(self.0, self.1),
            Mapped {
                inner: Pair(self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.spec_parse(ibuf)
    }
}

impl<P1, P2> Consistency for super::Permute2<P1, P2> where P1: Consistency, P2: Consistency {
    type Val = (P1::Val, P2::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Pair(self.0, self.1).consistent(v)
    }
}

impl<P1, P2> SpecSerializerDps for super::Permute2<P1, P2> where
    P1: SpecSerializerDps,
    P2: SpecSerializerDps,
 {
    type ST = (P1::ST, P2::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Pair(self.0, self.1).spec_serialize_dps(v, obuf)
    }
}

impl<P1, P2> SpecSerializer for super::Permute2<P1, P2> where
    P1: SpecSerializer,
    P2: SpecSerializer,
 {
    type SVal = (P1::SVal, P2::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Pair(self.0, self.1).spec_serialize(v)
    }
}

impl<P1, P2> Unambiguity for super::Permute2<P1, P2> where P1: Unambiguity, P2: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        let inner = Alt(
            Pair(self.0, self.1),
            Mapped {
                inner: Pair(self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.unambiguous()
    }
}

impl<P1, P2> NonTailFmt for super::Permute2<P1, P2> where P1: NonTailFmt, P2: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, self.1).lemma_serialize_dps_len(v, obuf);
    }
}

impl<P1, P2> GoodSerializer for super::Permute2<P1, P2> where
    P1: GoodSerializer,
    P2: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Pair(self.0, self.1).lemma_serialize_len(v);
    }
}

impl<P1: SpecByteLen, P2: SpecByteLen> SpecByteLen for super::Permute2<P1, P2> {
    type T = (P1::T, P2::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Pair(self.0, self.1).byte_len(v)
    }
}

impl<P1: StaticByteLen, P2: StaticByteLen> StaticByteLen for super::Permute2<P1, P2> {
    open spec fn static_byte_len() -> nat {
        P1::static_byte_len() + P2::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.0.lemma_static_len_matches_byte_len(v.0);
        self.1.lemma_static_len_matches_byte_len(v.1);
    }
}

// ============== Permute3 ==============
// Permute3(A, B, C) ::= Alt(
//     (A, Permute2(B, C)),
//     Alt(
//         Mapped((B, Permute2(A, C)), swap3_1),
//         Mapped((C, Permute2(A, B)), swap3_2),
//     )
// )
impl<A, B, C> SpecParser for super::Permute3<A, B, C> where
    A: SpecParser,
    B: SpecParser,
    C: SpecParser,
 {
    type PVal = (A::PVal, (B::PVal, C::PVal));

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let inner = Alt(
            Pair(self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: Pair(self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: Pair(self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.spec_parse(ibuf)
    }
}

impl<A, B, C> Consistency for super::Permute3<A, B, C> where
    A: Consistency,
    B: Consistency,
    C: Consistency,
 {
    type Val = (A::Val, (B::Val, C::Val));

    open spec fn consistent(&self, v: Self::Val) -> bool {
        Pair(self.0, Pair(self.1, self.2)).consistent(v)
    }
}

impl<A, B, C> SpecSerializerDps for super::Permute3<A, B, C> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
    C: SpecSerializerDps,
 {
    type ST = (A::ST, (B::ST, C::ST));

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Pair(self.0, super::Permute2(self.1, self.2)).spec_serialize_dps(v, obuf)
    }
}

impl<A, B, C> SpecSerializer for super::Permute3<A, B, C> where
    A: SpecSerializer,
    B: SpecSerializer,
    C: SpecSerializer,
 {
    type SVal = (A::SVal, (B::SVal, C::SVal));

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Pair(self.0, super::Permute2(self.1, self.2)).spec_serialize(v)
    }
}

impl<A, B, C> Unambiguity for super::Permute3<A, B, C> where
    A: Unambiguity,
    B: Unambiguity,
    C: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        let inner = Alt(
            Pair(self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: Pair(self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: Pair(self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.unambiguous()
    }
}

impl<A, B, C> NonTailFmt for super::Permute3<A, B, C> where
    A: NonTailFmt,
    B: NonTailFmt,
    C: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
        &&& self.2.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, super::Permute2(self.1, self.2)).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, super::Permute2(self.1, self.2)).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, C> GoodSerializer for super::Permute3<A, B, C> where
    A: GoodSerializer,
    B: GoodSerializer,
    C: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
        &&& self.2.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Pair(self.0, super::Permute2(self.1, self.2)).lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen, C: SpecByteLen> SpecByteLen for super::Permute3<A, B, C> {
    type T = (A::T, (B::T, C::T));

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Pair(self.0, super::Permute2(self.1, self.2)).byte_len(v)
    }
}

impl<A: StaticByteLen, B: StaticByteLen, C: StaticByteLen> StaticByteLen for super::Permute3<
    A,
    B,
    C,
> {
    open spec fn static_byte_len() -> nat {
        A::static_byte_len() + <super::Permute2<B, C> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.0.lemma_static_len_matches_byte_len(v.0);
        self.1.lemma_static_len_matches_byte_len(v.1.0);
        self.2.lemma_static_len_matches_byte_len(v.1.1);
    }
}

// ============== Permute4 ==============
// Permute4(A, B, C, D) ::= Alt(
//     (A, Permute3(B, C, D)),
//     Alt(
//         Mapped((B, Permute3(A, C, D)), swap4_1),
//         Alt(
//             Mapped((C, Permute3(A, B, D)), swap4_2),
//             Mapped((D, Permute3(A, B, C)), swap4_3),
//         )
//     )
// )
impl<A, B, C, D> SpecParser for super::Permute4<A, B, C, D> where
    A: SpecParser,
    B: SpecParser,
    C: SpecParser,
    D: SpecParser,
 {
    type PVal = (A::PVal, (B::PVal, (C::PVal, D::PVal)));

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        let inner = Alt(
            Pair(self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: Pair(self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: Pair(self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: Pair(self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.spec_parse(ibuf)
    }
}

impl<A, B, C, D> Consistency for super::Permute4<A, B, C, D> where
    A: Consistency,
    B: Consistency,
    C: Consistency,
    D: Consistency,
 {
    type Val = (A::Val, (B::Val, (C::Val, D::Val)));

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v.0) && self.1.consistent(v.1.0) && self.2.consistent(v.1.1.0)
            && self.3.consistent(v.1.1.1)
    }
}

impl<A, B, C, D> SpecSerializerDps for super::Permute4<A, B, C, D> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
    C: SpecSerializerDps,
    D: SpecSerializerDps,
 {
    type ST = (A::ST, (B::ST, (C::ST, D::ST)));

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).spec_serialize_dps(v, obuf)
    }
}

impl<A, B, C, D> SpecSerializer for super::Permute4<A, B, C, D> where
    A: SpecSerializer,
    B: SpecSerializer,
    C: SpecSerializer,
    D: SpecSerializer,
 {
    type SVal = (A::SVal, (B::SVal, (C::SVal, D::SVal)));

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).spec_serialize(v)
    }
}

impl<A, B, C, D> Unambiguity for super::Permute4<A, B, C, D> where
    A: Unambiguity,
    B: Unambiguity,
    C: Unambiguity,
    D: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        let inner = Alt(
            Pair(self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: Pair(self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: Pair(self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: Pair(self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.unambiguous()
    }
}

impl<A, B, C, D> NonTailFmt for super::Permute4<A, B, C, D> where
    A: NonTailFmt,
    B: NonTailFmt,
    C: NonTailFmt,
    D: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
        &&& self.2.serialize_dps_inv()
        &&& self.3.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, C, D> GoodSerializer for super::Permute4<A, B, C, D> where
    A: GoodSerializer,
    B: GoodSerializer,
    C: GoodSerializer,
    D: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
        &&& self.2.serialize_inv()
        &&& self.3.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).lemma_serialize_len(v);
    }
}

impl<
    A: SpecByteLen,
    B: SpecByteLen,
    C: SpecByteLen,
    D: SpecByteLen,
> SpecByteLen for super::Permute4<A, B, C, D> {
    type T = (A::T, (B::T, (C::T, D::T)));

    open spec fn byte_len(&self, v: Self::T) -> nat {
        Pair(self.0, super::Permute3(self.1, self.2, self.3)).byte_len(v)
    }
}

impl<
    A: StaticByteLen,
    B: StaticByteLen,
    C: StaticByteLen,
    D: StaticByteLen,
> StaticByteLen for super::Permute4<A, B, C, D> {
    open spec fn static_byte_len() -> nat {
        A::static_byte_len() + <super::Permute3<B, C, D> as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.0.lemma_static_len_matches_byte_len(v.0);
        self.1.lemma_static_len_matches_byte_len(v.1.0);
        self.2.lemma_static_len_matches_byte_len(v.1.1.0);
        self.3.lemma_static_len_matches_byte_len(v.1.1.1);
    }
}

} // verus!
