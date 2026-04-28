use crate::combinators::mapped::spec::*;
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

impl<A, B> SpecParser for super::Pair<A, B> where A: SpecParser, B: SpecParser {
    type PVal = (A::PVal, B::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, v1)) => match self.1.spec_parse(ibuf.skip(n1)) {
                Some((n2, v2)) => Some((n1 + n2, (v1, v2))),
                None => None,
            },
            None => None,
        }
    }
}

impl<A, B> Consistency for super::Pair<A, B> where A: Consistency, B: Consistency {
    type Val = (A::Val, B::Val);

    open spec fn consistent(&self, v: Self::Val) -> bool {
        self.0.consistent(v.0) && self.1.consistent(v.1)
    }
}

impl<A, B> SafeParser for super::Pair<A, B> where A: SafeParser, B: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& self.1.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        assert(self.safe_inv());
        self.0.lemma_parse_safe(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_safe(ibuf.skip(n1));
        }
    }
}

impl<A, B> SoundParser for super::Pair<A, B> where A: SoundParser, B: SoundParser {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& self.1.sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_sound_consumption(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, v1)) = self.0.spec_parse(ibuf) {
            self.1.lemma_parse_sound_value(ibuf.skip(n1));
        }
    }
}

impl<A, B> SpecSerializerDps for super::Pair<A, B> where
    A: SpecSerializerDps,
    B: SpecSerializerDps,
 {
    type SValue = (A::SValue, B::SValue);

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        self.0.spec_serialize_dps(v.0, self.1.spec_serialize_dps(v.1, obuf))
    }
}

impl<A, B> SpecSerializer for super::Pair<A, B> where A: SpecSerializer, B: SpecSerializer {
    type SVal = (A::SVal, B::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        self.0.spec_serialize(v.0) + self.1.spec_serialize(v.1)
    }
}

impl<A, B> NonTailFmt for super::Pair<A, B> where A: NonTailFmt, B: NonTailFmt {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& self.1.serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        let serialized0 = self.0.spec_serialize_dps(v.0, serialized1);
        assert(self.serialize_dps_inv());
        self.1.lemma_serialize_dps_prepend(v.1, obuf);
        self.0.lemma_serialize_dps_prepend(v.0, serialized1);
        let witness1 = choose|wit1: Seq<u8>| self.1.spec_serialize_dps(v.1, obuf) == wit1 + obuf;
        let witness0 = choose|wit0: Seq<u8>|
            self.0.spec_serialize_dps(v.0, serialized1) == wit0 + serialized1;
        assert(serialized0 == witness0 + witness1 + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        assert(self.serialize_dps_inv());
        self.1.lemma_serialize_dps_len(v.1, obuf);
        let serialized1 = self.1.spec_serialize_dps(v.1, obuf);
        self.0.lemma_serialize_dps_len(v.0, serialized1);
    }
}

impl<A, B> GoodSerializer for super::Pair<A, B> where A: GoodSerializer, B: GoodSerializer {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& self.1.serialize_inv()
    }

    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        assert(self.serialize_inv());
        self.1.lemma_serialize_len(v.1);
        self.0.lemma_serialize_len(v.0);
    }
}

impl<A: SpecByteLen, B: SpecByteLen> SpecByteLen for super::Pair<A, B> {
    type T = (A::T, B::T);

    open spec fn byte_len(&self, v: Self::T) -> nat {
        self.0.byte_len(v.0) + self.1.byte_len(v.1)
    }
}

impl<A: ValueByteLen, B: ValueByteLen> ValueByteLen for super::Pair<A, B> {
    open spec fn value_byte_len(v: Self::T) -> nat {
        A::value_byte_len(v.0) + B::value_byte_len(v.1)
    }

    proof fn lemma_value_len_matches_byte_len(&self, v: Self::T) {
        self.0.lemma_value_len_matches_byte_len(v.0);
        self.1.lemma_value_len_matches_byte_len(v.1);
    }
}

impl<A: StaticByteLen, B: StaticByteLen> StaticByteLen for super::Pair<A, B> {
    open spec fn static_byte_len() -> nat {
        A::static_byte_len() + B::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, v: Self::T) {
        self.0.lemma_static_len_matches_byte_len(v.0);
        self.1.lemma_static_len_matches_byte_len(v.1);
    }
}

impl<A, B> SpecParser for super::Bind<A, B> where
    A: SpecParser,
    B: SpecMap<Input = A::PVal>,
    B::Output: SpecParser,
 {
    type PVal = (A::PVal, <B::Output as SpecParser>::PVal);

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, key)) => {
                let next = self.1.spec_map(key);
                match next.spec_parse(ibuf.skip(n1)) {
                    Some((n2, val)) => Some((n1 + n2, (key, val))),
                    None => None,
                }
            },
            None => None,
        }
    }
}

impl<A, B> Consistency for super::Bind<A, B> where
    A: Consistency,
    B: SpecMap<Input = A::Val>,
    B::Output: Consistency,
 {
    type Val = (A::Val, <B::Output as Consistency>::Val);

    open spec fn consistent(&self, value: Self::Val) -> bool {
        let (key, val) = value;
        self.0.consistent(key) && self.1.spec_map(key).consistent(val)
    }
}

impl<A, B> SafeParser for super::Bind<A, B> where
    A: SafeParser,
    B: SpecMap<Input = A::PVal>,
    B::Output: SafeParser,
 {
    open spec fn safe_inv(&self) -> bool {
        &&& self.0.safe_inv()
        &&& forall|key: A::PVal| #[trigger] self.1.spec_map(key).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        assert(self.safe_inv());
        self.0.lemma_parse_safe(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let next = self.1.spec_map(key);
            next.lemma_parse_safe(ibuf.skip(n1));
        }
    }
}

impl<A, B> SoundParser for super::Bind<A, B> where
    A: SoundParser,
    B: SpecMap<Input = A::PVal>,
    B::Output: SoundParser,
 {
    open spec fn sound_inv(&self) -> bool {
        &&& self.0.sound_inv()
        &&& forall|key: A::PVal| #[trigger] self.1.spec_map(key).sound_inv()
    }

    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_consumption(ibuf);
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let next = self.1.spec_map(key);
            next.lemma_parse_sound_consumption(ibuf.skip(n1));
            next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((_n2, val)) = next.spec_parse(ibuf.skip(n1)) {
                assert(self.byte_len((key, val)) == self.0.byte_len(key) + next.byte_len(val));
            }
        }
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_sound_value(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let next = self.1.spec_map(key);
            next.lemma_parse_sound_value(ibuf.skip(n1));
            if let Some((_n2, val)) = next.spec_parse(ibuf.skip(n1)) {
                assert(self.consistent((key, val)));
            }
        }
    }
}

impl<A, B> SpecSerializerDps for super::Bind<A, B> where
    A: SpecSerializerDps,
    B: SpecMap<Input = A::SValue>,
    B::Output: SpecSerializerDps,
 {
    type SValue = (A::SValue, <B::Output as SpecSerializerDps>::SValue);

    open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        self.0.spec_serialize_dps(key, next.spec_serialize_dps(val, obuf))
    }
}

impl<A, B> SpecSerializer for super::Bind<A, B> where
    A: SpecSerializer,
    B: SpecMap<Input = A::SVal>,
    B::Output: SpecSerializer,
 {
    type SVal = (A::SVal, <B::Output as SpecSerializer>::SVal);

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        let (key, val) = v;
        let next = self.1.spec_map(key);
        self.0.spec_serialize(key) + next.spec_serialize(val)
    }
}

impl<A, B> NonTailFmt for super::Bind<A, B> where
    A: NonTailFmt,
    B: SpecMap<Input = A::SValue>,
    B::Output: NonTailFmt,
 {
    open spec fn serialize_dps_inv(&self) -> bool {
        &&& self.0.serialize_dps_inv()
        &&& forall|key: A::SValue| #[trigger] self.1.spec_map(key).serialize_dps_inv()
    }

    proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        let next_buf = next.spec_serialize_dps(val, obuf);

        assert(self.serialize_dps_inv());
        next.lemma_serialize_dps_prepend(val, obuf);
        self.0.lemma_serialize_dps_prepend(key, next_buf);

        let witness_next = choose|w: Seq<u8>| next.spec_serialize_dps(val, obuf) == w + obuf;
        let witness_prefix = choose|w: Seq<u8>|
            self.0.spec_serialize_dps(key, next_buf) == w + next_buf;
        assert(self.spec_serialize_dps(value, obuf) == witness_prefix + witness_next + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        let next_buf = next.spec_serialize_dps(val, obuf);
        assert(self.serialize_dps_inv());
        next.lemma_serialize_dps_len(val, obuf);
        self.0.lemma_serialize_dps_len(key, next_buf);
    }
}

impl<A, B> GoodSerializer for super::Bind<A, B> where
    A: GoodSerializer,
    B: SpecMap<Input = A::SVal>,
    B::Output: GoodSerializer,
 {
    open spec fn serialize_inv(&self) -> bool {
        &&& self.0.serialize_inv()
        &&& forall|key: A::SVal| #[trigger] self.1.spec_map(key).serialize_inv()
    }

    proof fn lemma_serialize_len(&self, value: Self::SVal) {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        assert(self.serialize_inv());
        self.0.lemma_serialize_len(key);
        next.lemma_serialize_len(val);
    }
}

impl<A, B> SpecByteLen for super::Bind<A, B> where
    A: SpecByteLen,
    B: SpecMap<Input = A::T>,
    B::Output: SpecByteLen,
 {
    type T = (A::T, <B::Output as SpecByteLen>::T);

    open spec fn byte_len(&self, value: Self::T) -> nat {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        self.0.byte_len(key) + next.byte_len(val)
    }
}

impl<A, B> ValueByteLen for super::Bind<A, B> where
    A: ValueByteLen,
    B: SpecMap<Input = A::T>,
    B::Output: ValueByteLen,
 {
    open spec fn value_byte_len(value: Self::T) -> nat {
        A::value_byte_len(value.0) + <B::Output as ValueByteLen>::value_byte_len(value.1)
    }

    proof fn lemma_value_len_matches_byte_len(&self, value: Self::T) {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        self.0.lemma_value_len_matches_byte_len(key);
        next.lemma_value_len_matches_byte_len(val);
    }
}

impl<A, B> StaticByteLen for super::Bind<A, B> where
    A: StaticByteLen,
    B: SpecMap<Input = A::T>,
    B::Output: StaticByteLen,
 {
    open spec fn static_byte_len() -> nat {
        A::static_byte_len() + <B::Output as StaticByteLen>::static_byte_len()
    }

    proof fn lemma_static_len_matches_byte_len(&self, value: Self::T) {
        let (key, val) = value;
        let next = self.1.spec_map(key);
        self.0.lemma_static_len_matches_byte_len(key);
        next.lemma_static_len_matches_byte_len(val);
    }
}

} // verus!
