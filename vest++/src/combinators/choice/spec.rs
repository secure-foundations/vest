use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: SpecParser, B: SpecParser> SpecParser for super::Choice<A, B> {
    type PVal = Either<A::PVal, B::PVal>;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n, va)) => Some((n, Either::Left(va))),
            None => match self.1.spec_parse(ibuf) {
                Some((n, vb)) => Some((n, Either::Right(vb))),
                None => None,
            },
        }
    }
}

impl<A: GoodParser, B: GoodParser> GoodParser for super::Choice<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        self.1.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_wf(ibuf);
        self.1.lemma_parse_wf(ibuf);
    }
}

impl<A, B> SpecSerializerDps for super::Choice<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type ST = Either<A::ST, B::ST>;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize_dps(va, obuf),
            Either::Right(vb) => self.1.spec_serialize_dps(vb, obuf),
        }
    }
}

impl<A, B> SpecSerializer for super::Choice<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = Either<A::SVal, B::SVal>;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        match v {
            Either::Left(va) => self.0.spec_serialize(va),
            Either::Right(vb) => self.1.spec_serialize(vb),
        }
    }
}

impl<A, B> Serializability for super::Choice<A, B> where
    A: Serializability + SpecParser,
    B: Serializability,
 {
    #[verusfmt::skip]
    open spec fn serializable(&self, v: Self::ST, obuf: Seq<u8>) -> bool {
        match v {
            Either::Left(va) => self.0.serializable(va, obuf),
            Either::Right(vb) => {
                &&& self.1.serializable(vb, obuf)
                // To ensure the parser can recover the choice made during serialization
                &&& self.0.spec_parse(self.1.spec_serialize_dps(vb, obuf)) is None
            },
        }
    }
}

impl<A: Unambiguity, B: Unambiguity> Unambiguity for super::Choice<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> GoodSerializerDps for super::Choice<A, B> where
    A: GoodSerializerDps,
    B: GoodSerializerDps,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Either::Left(va) => {
                self.0.lemma_serialize_dps_buf(va, obuf);
            },
            Either::Right(vb) => {
                self.1.lemma_serialize_dps_buf(vb, obuf);
            },
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        match v {
            Either::Left(va) => {
                self.0.lemma_serialize_dps_len(va, obuf);
            },
            Either::Right(vb) => {
                self.1.lemma_serialize_dps_len(vb, obuf);
            },
        }
    }
}

impl<A: GoodSerializer, B: GoodSerializer> GoodSerializer for super::Choice<A, B> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        match v {
            Either::Left(va) => {
                self.0.lemma_serialize_len(va);
            },
            Either::Right(vb) => {
                self.1.lemma_serialize_len(vb);
            },
        }
    }
}

impl<A, B> SpecByteLen for super::Choice<A, B> where A: SpecByteLen, B: SpecByteLen {
    type T = Either<A::T, B::T>;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        match v {
            Either::Left(va) => self.0.byte_len(va),
            Either::Right(vb) => self.1.byte_len(vb),
        }
    }
}

impl<A: SpecParser, B: SpecParser<PVal = A::PVal>> SpecParser for super::Alt<A, B> {
    type PVal = A::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        if let None = self.0.spec_parse(ibuf) {
            self.1.spec_parse(ibuf)
        } else {
            self.0.spec_parse(ibuf)
        }
    }
}

impl<A: GoodParser, B: GoodParser<PVal = A::PVal>> GoodParser for super::Alt<A, B> {
    proof fn lemma_parse_length(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_length(ibuf);
        self.1.lemma_parse_length(ibuf);
    }

    proof fn lemma_parse_wf(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_wf(ibuf);
        self.1.lemma_parse_wf(ibuf);
    }
}

pub open spec fn triv(b: bool) -> bool {
    true
}

impl<A, B> SpecSerializerDps for super::Alt<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps<ST = A::ST>,
 {
    type ST = A::ST;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.spec_serialize_dps(v, obuf)
        } else {
            self.1.spec_serialize_dps(v, obuf)
        }
    }
}

impl<A: Unambiguity, B: Unambiguity<PVal = A::PVal>> Unambiguity for super::Alt<A, B> {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& self.1.unambiguous()
        &&& disjoint_domains(self.0, self.1)
    }
}

impl<A, B> GoodSerializerDps for super::Alt<A, B> where
    A: GoodSerializerDps,
    B: GoodSerializerDps<T = A::T>,
 {
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.lemma_serialize_dps_buf(v, obuf)
        } else {
            self.1.lemma_serialize_dps_buf(v, obuf)
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.lemma_serialize_dps_len(v, obuf)
        } else {
            self.1.lemma_serialize_dps_len(v, obuf)
        }
    }
}

impl<A, B> SpecSerializer for super::Alt<A, B> where
    A: SpecSerializer,
    B: SpecSerializer<SVal = A::SVal>,
 {
    type SVal = A::SVal;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.spec_serialize(v)
        } else {
            self.1.spec_serialize(v)
        }
    }
}

impl<A, B> GoodSerializer for super::Alt<A, B> where
    A: GoodSerializer,
    B: GoodSerializer<T = A::T>,
 {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.lemma_serialize_len(v)
        } else {
            self.1.lemma_serialize_len(v)
        }
    }
}

impl<A, B> SpecByteLen for super::Alt<A, B> where A: SpecByteLen, B: SpecByteLen<T = A::T> {
    type T = A::T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        let b = choose|flip: bool| triv(flip);
        if b {
            self.0.byte_len(v)
        } else {
            self.1.byte_len(v)
        }
    }
}

} // verus!
