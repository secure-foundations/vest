use crate::core::spec::{
    Consistency, GoodParser, PredFnSpec, SpecByteLen, SpecParser, SpecSerializer,
    SpecSerializerDps, Unambiguity,
};
use vstd::prelude::*;

verus! {

pub type ByteLenFnSpec<T> = spec_fn(T) -> nat;

pub type ParserFnSpec<T> = spec_fn(Seq<u8>) -> Option<(int, T)>;

pub type SerializerDPSFnSpec<T> = spec_fn(T, Seq<u8>) -> Seq<u8>;

pub type SerializerFnSpec<T> = spec_fn(T) -> Seq<u8>;

impl<T> Consistency for PredFnSpec<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self)(v)
    }
}

impl<T> SpecByteLen for ByteLenFnSpec<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self)(v)
    }
}

impl<T> SpecParser for ParserFnSpec<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self)(ibuf)
    }
}

impl<T> SpecSerializerDps for SerializerDPSFnSpec<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self)(v, obuf)
    }
}

impl<T> SpecSerializer for SerializerFnSpec<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self)(v)
    }
}

pub type ParserSpecs<T> = (ParserFnSpec<T>, PredFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for ParserSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.2)(v)
    }
}

impl<T> SpecParser for ParserSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0)(ibuf)
    }
}

impl<T> Consistency for ParserSpecs<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.1)(v)
    }
}

impl<T> GoodParser for ParserSpecs<T> {
    open spec fn inv(&self) -> bool {
        let (p_fn, c_fn, len_fn) = *self;
        forall|i: Seq<u8>| #[trigger]
            (p_fn)(i) matches Some((n, v)) ==> {
                &&& 0 <= n <= i.len()
                &&& n == (len_fn)(v)
                &&& (c_fn)(v)
            }
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
    }
}

/// A well-behaved DPS serializer that satisfies key properties.
///
/// This is tailored for function-backed serializer specs and intentionally named
/// differently from [`crate::core::spec::GoodSerializerDps`] for compatibility.
pub trait WfSerializerDps: SpecByteLen + SpecSerializerDps<ST = Self::T> {
    open spec fn ih(&self) -> bool {
        true
    }

    /// Lemma: serializer *prepends* to the output buffer
    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.ih(),
        ensures
            exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf,
    ;

    /// Lemma: serializer produces buffer of the correct length
    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>)
        requires
            self.ih(),
        ensures
            self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v),
    ;
}

pub type SerializerDPSSpecs<T> = (SerializerDPSFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for SerializerDPSSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecSerializerDps for SerializerDPSSpecs<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.0)(v, obuf)
    }
}

impl<T> WfSerializerDps for SerializerDPSSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T, obuf: Seq<u8>|
            {
                &&& exists|new_buf: Seq<u8>| #[trigger]
                    self.spec_serialize_dps(v, obuf) == new_buf + obuf
                &&& self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v)
            }
    }

    proof fn lemma_serialize_dps_buf(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(exists|new_buf: Seq<u8>| self.spec_serialize_dps(v, obuf) == new_buf + obuf) by {
            let new_buf = choose|new_buf: Seq<u8>| #[trigger]
                self.spec_serialize_dps(v, obuf) == new_buf + obuf;
            assert(self.spec_serialize_dps(v, obuf) == new_buf + obuf);
        }
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::ST, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf).len() - obuf.len() == self.byte_len(v));
    }
}

/// A well-behaved serializer that satisfies key properties.
///
/// This is tailored for function-backed serializer specs and intentionally named
/// differently from [`crate::core::spec::GoodSerializer`] for compatibility.
pub trait WfSerializer: SpecByteLen + SpecSerializer<SVal = Self::T> {
    open spec fn ih(&self) -> bool {
        true
    }

    /// Lemma: serializer produces buffer of the correct length
    proof fn lemma_serialize_len(&self, v: Self::SVal)
        requires
            self.ih(),
        ensures
            self.spec_serialize(v).len() == self.byte_len(v),
    ;
}

pub type SerializerSpecs<T> = (SerializerFnSpec<T>, ByteLenFnSpec<T>);

impl<T> SpecByteLen for SerializerSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecSerializer for SerializerSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.0)(v)
    }
}

impl<T> WfSerializer for SerializerSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T| #[trigger] self.spec_serialize(v).len() == self.byte_len(v)
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.spec_serialize(v).len() == self.byte_len(v));
    }
}

pub type UnambiguityFnSpec = spec_fn() -> bool;

#[verusfmt::skip]
pub trait WfSPRoundTripDps where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializerDps<ST = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
{
    open spec fn ih(&self) -> bool {
        true
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>)
        requires
            self.ih(),
            self.unambiguous(),
            self.consistent(v),
        ensures
            ({
                let ibuf = self.spec_serialize_dps(v, obuf);
                let n = self.byte_len(v) as int;
                self.spec_parse(ibuf) == Some((n, v))
            }),
    ;
}

pub type SPRoundTripDpsSpecs<T> = (
    ParserFnSpec<T>,
    PredFnSpec<T>,
    ByteLenFnSpec<T>,
    SerializerDPSFnSpec<T>,
    UnambiguityFnSpec,
);

impl<T> SpecByteLen for SPRoundTripDpsSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.2)(v)
    }
}

impl<T> SpecParser for SPRoundTripDpsSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0)(ibuf)
    }
}

impl<T> SpecSerializerDps for SPRoundTripDpsSpecs<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.3)(v, obuf)
    }
}

impl<T> Consistency for SPRoundTripDpsSpecs<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.1)(v)
    }
}

impl<T> Unambiguity for SPRoundTripDpsSpecs<T> {
    open spec fn unambiguous(&self) -> bool {
        (self.4)()
    }
}

impl<T> WfSPRoundTripDps for SPRoundTripDpsSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T, obuf: Seq<u8>| #[trigger]
            self.spec_parse(self.spec_serialize_dps(v, obuf)) == Some((self.byte_len(v) as int, v))
    }

    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        assert(self.spec_parse(self.spec_serialize_dps(v, obuf)) == Some(
            (self.byte_len(v) as int, v),
        ));
    }
}

#[verusfmt::skip]
pub trait WfSPRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          Consistency<Val = Self::T> +
          Unambiguity,
{
    open spec fn ih(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T)
        requires
            self.ih(),
            self.unambiguous(),
            self.consistent(v),
        ensures
            ({
                let bytes = self.spec_serialize(v);
                self.spec_parse(bytes) == Some((bytes.len() as int, v))
            }),
    ;
}

pub type SPRoundTripSpecs<T> = (
    ParserFnSpec<T>,
    PredFnSpec<T>,
    ByteLenFnSpec<T>,
    SerializerFnSpec<T>,
    UnambiguityFnSpec,
);

impl<T> SpecByteLen for SPRoundTripSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.2)(v)
    }
}

impl<T> SpecParser for SPRoundTripSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0)(ibuf)
    }
}

impl<T> SpecSerializer for SPRoundTripSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.3)(v)
    }
}

impl<T> Consistency for SPRoundTripSpecs<T> {
    type Val = T;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        (self.1)(v)
    }
}

impl<T> Unambiguity for SPRoundTripSpecs<T> {
    open spec fn unambiguous(&self) -> bool {
        (self.4)()
    }
}

impl<T> WfSPRoundTrip for SPRoundTripSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T| #[trigger]
            self.spec_parse(self.spec_serialize(v)) == Some(
                (self.spec_serialize(v).len() as int, v),
            )
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::T) {
        let bytes = self.spec_serialize(v);
        assert(self.spec_parse(bytes) == Some((bytes.len() as int, v)));
    }
}

#[verusfmt::skip]
pub trait WfPSRoundTrip where
    Self: SpecByteLen +
          SpecParser<PVal = Self::T> +
          SpecSerializer<SVal = Self::T> +
          Unambiguity,
{
    open spec fn ih(&self) -> bool {
        true
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>)
        requires
            self.ih(),
            self.unambiguous(),
        ensures
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize(v) == ibuf.take(n),
    ;

    proof fn corollary_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.ih(),
            self.unambiguous(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==>
            self.spec_parse(buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    {
        self.theorem_parse_serialize_roundtrip(buf1);
        self.theorem_parse_serialize_roundtrip(buf2);
    }
}

pub type PSRoundTripSpecs<T> = (
    ParserFnSpec<T>,
    ByteLenFnSpec<T>,
    SerializerFnSpec<T>,
    UnambiguityFnSpec,
);

impl<T> SpecByteLen for PSRoundTripSpecs<T> {
    type T = T;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        (self.1)(v)
    }
}

impl<T> SpecParser for PSRoundTripSpecs<T> {
    type PVal = T;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (self.0)(ibuf)
    }
}

impl<T> SpecSerializer for PSRoundTripSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.2)(v)
    }
}

impl<T> Unambiguity for PSRoundTripSpecs<T> {
    open spec fn unambiguous(&self) -> bool {
        (self.3)()
    }
}

impl<T> WfPSRoundTrip for PSRoundTripSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|ibuf: Seq<u8>| #[trigger]
            self.spec_parse(ibuf) matches Some((n, v)) ==> self.spec_serialize(v) == ibuf.take(n)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, ibuf: Seq<u8>) {
        if let Some((n, v)) = self.spec_parse(ibuf) {
            assert(self.spec_serialize(v) == ibuf.take(n));
        }
    }
}

pub trait WfNonMalleable: SpecByteLen + SpecParser<PVal = Self::T> + Consistency<Val = Self::T> {
    open spec fn ih(&self) -> bool {
        true
    }

    #[verusfmt::skip]
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>)
        requires
            self.ih(),
        ensures
            self.spec_parse(buf1) matches Some((n1, v1)) ==>
            self.spec_parse(buf2) matches Some((n2, v2)) ==>
            v1 == v2 ==> buf1.take(n1) == buf2.take(n2),
    ;
}

pub type NonMalleableSpecs<T> = ParserSpecs<T>;

impl<T> WfNonMalleable for NonMalleableSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|buf1: Seq<u8>, buf2: Seq<u8>| #[trigger]
            self.spec_parse(buf1) matches Some((n1, v1)) ==> #[trigger] self.spec_parse(
                buf2,
            ) matches Some((n2, v2)) ==> v1 == v2 ==> buf1.take(n1) == buf2.take(n2)
    }

    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        if let Some((n1, v1)) = self.spec_parse(buf1) {
            if let Some((n2, v2)) = self.spec_parse(buf2) {
                if v1 == v2 {
                    assert(buf1.take(n1) == buf2.take(n2));
                }
            }
        }
    }
}

pub trait WfEquivSerializersGeneral: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    open spec fn ih(&self) -> bool {
        true
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>)
        requires
            self.ih(),
        ensures
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf,
    ;
}

pub type EquivSerializersGeneralSpecs<T> = (SerializerFnSpec<T>, SerializerDPSFnSpec<T>);

impl<T> SpecSerializer for EquivSerializersGeneralSpecs<T> {
    type SVal = T;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        (self.0)(v)
    }
}

impl<T> SpecSerializerDps for EquivSerializersGeneralSpecs<T> {
    type ST = T;

    open spec fn spec_serialize_dps(&self, v: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        (self.1)(v, obuf)
    }
}

impl<T> WfEquivSerializersGeneral for EquivSerializersGeneralSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T, obuf: Seq<u8>| #[trigger]
            self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf
    }

    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        assert(self.spec_serialize_dps(v, obuf) == self.spec_serialize(v) + obuf);
    }
}

pub trait WfEquivSerializers: SpecSerializer + SpecSerializerDps<ST = Self::SVal> {
    open spec fn ih(&self) -> bool {
        true
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal)
        requires
            self.ih(),
        ensures
            self.spec_serialize_dps(v, seq![]) == self.spec_serialize(v),
    ;
}

pub type EquivSerializersSpecs<T> = EquivSerializersGeneralSpecs<T>;

impl<T> WfEquivSerializers for EquivSerializersSpecs<T> {
    open spec fn ih(&self) -> bool {
        forall|v: T| #[trigger] self.spec_serialize_dps(v, seq![]) == self.spec_serialize(v)
    }

    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        assert(self.spec_serialize_dps(v, seq![]) == self.spec_serialize(v));
    }
}

} // verus!
