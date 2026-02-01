use crate::combinators::choice::Alt;
use crate::combinators::mapped::spec::{IsoMapper, Mapper};
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
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.spec_parse(ibuf)
    }
}

impl<P1, P2> GoodParser for super::Permute2<P1, P2> where P1: GoodParser, P2: GoodParser {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.lemma_parse_wf(ibuf);
    }
}

impl<P1, P2> SpecSerializerDps for super::Permute2<P1, P2> where
    P1: SpecSerializerDps,
    P2: SpecSerializerDps,
 {
    type ST = (P1::ST, P2::ST);

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let inner = Alt(
            (self.0, self.1),
            Mapped { inner: (self.1, self.0), mapper: Swap2Mapper::<P1::ST, P2::ST>(PhantomData) },
        );
        inner.spec_serialize_dps(v, obuf)
    }
}

impl<P1, P2> SpecSerializer for super::Permute2<P1, P2> where
    P1: SpecSerializer,
    P2: SpecSerializer,
 {
    type SVal = (P1::SVal, P2::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let inner = Alt(
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::SVal, P2::SVal>(PhantomData),
            },
        );
        inner.spec_serialize(v)
    }
}

impl<P1, P2> Unambiguity for super::Permute2<P1, P2> where P1: Unambiguity, P2: Unambiguity {
    open spec fn unambiguous(&self) -> bool {
        let inner = Alt(
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::PVal, P2::PVal>(PhantomData),
            },
        );
        inner.unambiguous()
    }
}

impl<P1, P2> GoodSerializerDps for super::Permute2<P1, P2> where
    P1: GoodSerializerDps,
    P2: GoodSerializerDps,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, self.1),
            Mapped { inner: (self.1, self.0), mapper: Swap2Mapper::<P1::ST, P2::ST>(PhantomData) },
        );
        inner.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, self.1),
            Mapped { inner: (self.1, self.0), mapper: Swap2Mapper::<P1::ST, P2::ST>(PhantomData) },
        );
        inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<P1, P2> GoodSerializer for super::Permute2<P1, P2> where
    P1: GoodSerializer,
    P2: GoodSerializer,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let inner = Alt(
            (self.0, self.1),
            Mapped {
                inner: (self.1, self.0),
                mapper: Swap2Mapper::<P1::SVal, P2::SVal>(PhantomData),
            },
        );
        inner.lemma_serialize_len(v);
    }
}

impl<P1: SpecByteLen, P2: SpecByteLen> SpecByteLen for super::Permute2<P1, P2> {
    type T = (P1::T, P2::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let inner = Alt(
            (self.0, self.1),
            Mapped { inner: (self.1, self.0), mapper: Swap2Mapper::<P1::T, P2::T>(PhantomData) },
        );
        inner.byte_len(v)
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
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.spec_parse(ibuf)
    }
}

impl<A, B, C> GoodParser for super::Permute3<A, B, C> where
    A: GoodParser,
    B: GoodParser,
    C: GoodParser,
 {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.lemma_parse_wf(ibuf);
    }
}

impl<A, B, C> SpecSerializerDps for super::Permute3<A, B, C> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
    C: SpecSerializerDps,
 {
    type ST = (A::ST, (B::ST, C::ST));

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::ST, B::ST, C::ST>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::ST, B::ST, C::ST>(PhantomData),
                },
            ),
        );
        inner.spec_serialize_dps(v, obuf)
    }
}

impl<A, B, C> SpecSerializer for super::Permute3<A, B, C> where
    A: SpecSerializer,
    B: SpecSerializer,
    C: SpecSerializer,
 {
    type SVal = (A::SVal, (B::SVal, C::SVal));

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::SVal, B::SVal, C::SVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::SVal, B::SVal, C::SVal>(PhantomData),
                },
            ),
        );
        inner.spec_serialize(v)
    }
}

impl<A, B, C> Unambiguity for super::Permute3<A, B, C> where
    A: Unambiguity,
    B: Unambiguity,
    C: Unambiguity,
 {
    open spec fn unambiguous(&self) -> bool {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::PVal, B::PVal, C::PVal>(PhantomData),
                },
            ),
        );
        inner.unambiguous()
    }
}

impl<A, B, C> GoodSerializerDps for super::Permute3<A, B, C> where
    A: GoodSerializerDps,
    B: GoodSerializerDps,
    C: GoodSerializerDps,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::ST, B::ST, C::ST>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::ST, B::ST, C::ST>(PhantomData),
                },
            ),
        );
        inner.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::ST, B::ST, C::ST>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::ST, B::ST, C::ST>(PhantomData),
                },
            ),
        );
        inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, C> GoodSerializer for super::Permute3<A, B, C> where
    A: GoodSerializer,
    B: GoodSerializer,
    C: GoodSerializer,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::SVal, B::SVal, C::SVal>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::SVal, B::SVal, C::SVal>(PhantomData),
                },
            ),
        );
        inner.lemma_serialize_len(v);
    }
}

impl<A: SpecByteLen, B: SpecByteLen, C: SpecByteLen> SpecByteLen for super::Permute3<A, B, C> {
    type T = (A::T, (B::T, C::T));

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let inner = Alt(
            (self.0, super::Permute2(self.1, self.2)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute2(self.0, self.2)),
                    mapper: Swap3Mapper1::<A::T, B::T, C::T>(PhantomData),
                },
                Mapped {
                    inner: (self.2, super::Permute2(self.0, self.1)),
                    mapper: Swap3Mapper2::<A::T, B::T, C::T>(PhantomData),
                },
            ),
        );
        inner.byte_len(v)
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
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.spec_parse(ibuf)
    }
}

impl<A, B, C, D> GoodParser for super::Permute4<A, B, C, D> where
    A: GoodParser,
    B: GoodParser,
    C: GoodParser,
    D: GoodParser,
 {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.lemma_parse_wf(ibuf);
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
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                ),
            ),
        );
        inner.spec_serialize_dps(v, obuf)
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
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.spec_serialize(v)
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
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::PVal, B::PVal, C::PVal, D::PVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.unambiguous()
    }
}

impl<A, B, C, D> GoodSerializerDps for super::Permute4<A, B, C, D> where
    A: GoodSerializerDps,
    B: GoodSerializerDps,
    C: GoodSerializerDps,
    D: GoodSerializerDps,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                ),
            ),
        );
        inner.lemma_serialize_dps_buf(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::ST, B::ST, C::ST, D::ST>(PhantomData),
                    },
                ),
            ),
        );
        inner.lemma_serialize_dps_len(v, obuf);
    }
}

impl<A, B, C, D> GoodSerializer for super::Permute4<A, B, C, D> where
    A: GoodSerializer,
    B: GoodSerializer,
    C: GoodSerializer,
    D: GoodSerializer,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::SVal, B::SVal, C::SVal, D::SVal>(PhantomData),
                    },
                ),
            ),
        );
        inner.lemma_serialize_len(v);
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
        let inner = Alt(
            (self.0, super::Permute3(self.1, self.2, self.3)),
            Alt(
                Mapped {
                    inner: (self.1, super::Permute3(self.0, self.2, self.3)),
                    mapper: Swap4Mapper1::<A::T, B::T, C::T, D::T>(PhantomData),
                },
                Alt(
                    Mapped {
                        inner: (self.2, super::Permute3(self.0, self.1, self.3)),
                        mapper: Swap4Mapper2::<A::T, B::T, C::T, D::T>(PhantomData),
                    },
                    Mapped {
                        inner: (self.3, super::Permute3(self.0, self.1, self.2)),
                        mapper: Swap4Mapper3::<A::T, B::T, C::T, D::T>(PhantomData),
                    },
                ),
            ),
        );
        inner.byte_len(v)
    }
}

} // verus!
