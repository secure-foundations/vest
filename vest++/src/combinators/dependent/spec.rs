use super::*;
use crate::combinators::bytes::ExactLen;
use crate::combinators::length::AsLen;
use crate::combinators::{Choice, Cond, Sum, Varied, Void};
use crate::core::spec::*;
use vstd::pervasive::arbitrary;
use vstd::prelude::*;

verus! {

impl<Head, Tail> SpecParser for Bind<Head, Tail> where
    Head: SpecParser,
    Tail: DepCombinator<Key = Head::PVal>,
    Tail::Body: SpecParser<PVal = Tail::Val>,
 {
    type PVal = Tail::Val;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(ibuf) {
            Some((n1, key)) => {
                let body = self.1.apply(key);
                match body.spec_parse(ibuf.skip(n1)) {
                    Some((n2, value)) => Some((n1 + n2, value)),
                    None => None,
                }
            },
            None => None,
        }
    }
}

impl<Head, Tail> Consistency for Bind<Head, Tail> where
    Head: Consistency,
    Tail: DepCombinator<Key = Head::Val>,
 {
    type Val = Tail::Val;

    open spec fn consistent(&self, value: Self::Val) -> bool {
        let key = self.1.recover(value);
        self.0.consistent(key) && self.1.apply(key).consistent(value)
    }
}

impl<Head, Tail> GoodParser for Bind<Head, Tail> where
    Head: GoodParser,
    Tail: DepCombinator<Key = Head::PVal>,
    Tail::Body: GoodParser<T = Tail::Val>,
 {
    open spec fn inv(&self) -> bool {
        &&& self.0.inv()
        &&& forall|key: Head::PVal| #[trigger] self.1.apply(key).inv()
    }

    proof fn lemma_parse_len_bound(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_len_bound(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let body = self.1.apply(key);
            body.lemma_parse_len_bound(ibuf.skip(n1));
        }
    }

    proof fn lemma_parse_byte_len(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_byte_len(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let body = self.1.apply(key);
            body.lemma_parse_byte_len(ibuf.skip(n1));
            body.lemma_parse_consistent(ibuf.skip(n1));
            if let Some((n2, value)) = body.spec_parse(ibuf.skip(n1)) {
                self.1.lemma_recover_consistent(key, value);
                assert(self.1.recover(value) == key);
                assert(self.byte_len(value) == self.0.byte_len(key) + body.byte_len(value));
            }
        }
    }

    proof fn lemma_parse_consistent(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_consistent(ibuf);
        if let Some((n1, key)) = self.0.spec_parse(ibuf) {
            let body = self.1.apply(key);
            body.lemma_parse_consistent(ibuf.skip(n1));
            if let Some((_n2, value)) = body.spec_parse(ibuf.skip(n1)) {
                self.1.lemma_recover_consistent(key, value);
                assert(self.1.recover(value) == key);
                assert(self.consistent(value));
            }
        }
    }
}

impl<Head, Tail> SpecSerializerDps for Bind<Head, Tail> where
    Head: SpecSerializerDps,
    Tail: DepCombinator<Key = Head::ST>,
    Tail::Body: SpecSerializerDps<ST = Tail::Val>,
 {
    type ST = Tail::Val;

    open spec fn spec_serialize_dps(&self, value: Self::ST, obuf: Seq<u8>) -> Seq<u8> {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        self.0.spec_serialize_dps(key, body.spec_serialize_dps(value, obuf))
    }
}

impl<Head, Tail> SpecSerializer for Bind<Head, Tail> where
    Head: SpecSerializer,
    Tail: DepCombinator<Key = Head::SVal>,
    Tail::Body: SpecSerializer<SVal = Tail::Val>,
 {
    type SVal = Tail::Val;

    open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        self.0.spec_serialize(key) + body.spec_serialize(value)
    }
}

impl<Head, Tail> Unambiguity for Bind<Head, Tail> where
    Head: Unambiguity,
    Tail: DepCombinator<Key = Head::PVal>,
    Tail::Body: Unambiguity + SpecParser<PVal = Tail::Val>,
 {
    open spec fn unambiguous(&self) -> bool {
        &&& self.0.unambiguous()
        &&& forall|key: Head::PVal| #[trigger] (self.1.apply(key)).unambiguous()
    }
}

impl<Head, Tail> GoodSerializerDps for Bind<Head, Tail> where
    Head: GoodSerializerDps,
    Tail: DepCombinator<Key = Head::ST>,
    Tail::Body: GoodSerializerDps<T = Tail::Val>,
 {
    proof fn lemma_serialize_dps_buf(&self, value: Self::ST, obuf: Seq<u8>) {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        let body_buf = body.spec_serialize_dps(value, obuf);

        body.lemma_serialize_dps_buf(value, obuf);
        self.0.lemma_serialize_dps_buf(key, body_buf);

        let witness_body = choose|w: Seq<u8>| body.spec_serialize_dps(value, obuf) == w + obuf;
        let witness_prefix = choose|w: Seq<u8>|
            self.0.spec_serialize_dps(key, body_buf) == w + body_buf;
        assert(self.spec_serialize_dps(value, obuf) == witness_prefix + witness_body + obuf);
    }

    proof fn lemma_serialize_dps_len(&self, value: Self::ST, obuf: Seq<u8>) {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        let body_buf = body.spec_serialize_dps(value, obuf);
        body.lemma_serialize_dps_len(value, obuf);
        self.0.lemma_serialize_dps_len(key, body_buf);
    }
}

impl<Head, Tail> GoodSerializer for Bind<Head, Tail> where
    Head: GoodSerializer,
    Tail: DepCombinator<Key = Head::SVal>,
    Tail::Body: GoodSerializer<T = Tail::Val>,
 {
    proof fn lemma_serialize_len(&self, value: Self::SVal) {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        self.0.lemma_serialize_len(key);
        body.lemma_serialize_len(value);
    }
}

impl<Head, Tail> SpecByteLen for Bind<Head, Tail> where
    Head: SpecByteLen,
    Tail: DepCombinator<Key = Head::T>,
    Tail::Body: SpecByteLen<T = Tail::Val>,
 {
    type T = Tail::Val;

    open spec fn byte_len(&self, value: Self::T) -> nat {
        let key = self.1.recover(value);
        let body = self.1.apply(key);
        self.0.byte_len(key) + body.byte_len(value)
    }
}

// ----To enable compositions like `Bind(T1, Bind(T2, ...))`---
// NOTE: The above is not true... but I will keep it here for fun
impl<Head, Nested> DepCombinator for Bind<Head, Nested> where
    Head: Consistency,
    Nested: DepCombinator<Key = Head::Val>,
 {
    type Key = Head::Val;

    type Val = Nested::Val;

    type Body = Nested::Body;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        self.1.apply(key)
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        self.1.recover(value)
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        self.1.lemma_recover_consistent(key, value);
    }
}

// Enabling patterns like `Bind(U8, VariedU8())`, `Bind(U16, VariedU16())`,
// and arbitrary user length types implementing `AsLen`.
impl<Len: AsLen> DepCombinator for VariedLen<Len> {
    type Key = Len;

    type Val = Seq<u8>;

    type Body = Varied<Len>;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        Varied(key)
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        Len::from_nat(value.len())
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        if self.apply(key).consistent(value) {
            Len::lemma_lossless_casting(key);
            assert(value.len() == key.as_usize());
            assert(value.len() == key.as_usize() as nat);
        }
    }
}

// Enabling Patterns like `Bind((H1, H2), (T1, T2))`.
// e.g.,
// ```
// fmt = {
//   @l1: u8,
//   @l2: u16,
//   payload1: [u8; @l1],
//   payload2: [u8; @l2],
// }
impl<D1: DepCombinator, D2: DepCombinator> DepCombinator for (D1, D2) {
    type Key = (D1::Key, D2::Key);

    type Val = (D1::Val, D2::Val);

    type Body = (D1::Body, D2::Body);

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        (self.0.apply(key.0), self.1.apply(key.1))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        (self.0.recover(value.0), self.1.recover(value.1))
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        self.0.lemma_recover_consistent(key.0, value.0);
        self.1.lemma_recover_consistent(key.1, value.1);
    }
}

impl<Tag, C, Rest> DepCombinator for TVOr<Tag, C, Rest> where
    C: Consistency,
    Rest: DepCombinator<Key = Tag>,
 {
    type Key = Tag;

    type Val = Sum<C::Val, Rest::Val>;

    type Body = Choice<Cond<C>, Rest::Body>;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        Choice(Cond(key == self.0, self.1), self.2.apply(key))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        match value {
            Sum::Inl(_) => self.0,
            Sum::Inr(vr) => self.2.recover(vr),
        }
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        if self.apply(key).consistent(value) {
            match value {
                Sum::Inl(vl) => {
                    assert(self.recover(value) == key);
                },
                Sum::Inr(vr) => {
                    self.2.lemma_recover_consistent(key, vr);
                },
            }
        }
    }
}

impl<Tag> DepCombinator for VoidTag<Tag> {
    type Key = Tag;

    type Val = !;

    type Body = Void;

    open spec fn apply(&self, _key: Self::Key) -> Self::Body {
        Void
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        arbitrary::<Tag>()
    }

    proof fn lemma_recover_consistent(&self, _key: Self::Key, value: Self::Val) {
    }
}

impl<Tag, Left, Right> DepCombinator for TagValNode<Tag, Left, Right> where
    Left: DepCombinator<Key = Tag>,
    Right: DepCombinator<Key = Tag>,
 {
    type Key = Tag;

    type Val = Sum<Left::Val, Right::Val>;

    type Body = Choice<Left::Body, Right::Body>;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        Choice(self.0.apply(key), self.1.apply(key))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        match value {
            Sum::Inl(vl) => self.0.recover(vl),
            Sum::Inr(vr) => self.1.recover(vr),
        }
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        match value {
            Sum::Inl(vl) => {
                self.0.lemma_recover_consistent(key, vl);
            },
            Sum::Inr(vr) => {
                self.1.lemma_recover_consistent(key, vr);
            },
        }
    }
}

impl<Tag, C: Consistency> DepCombinator for TVLeaf<Tag, C> {
    type Key = Tag;

    type Val = C::Val;

    type Body = Cond<C>;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        Cond(key == self.0, self.1)
    }

    open spec fn recover(&self, _value: Self::Val) -> Self::Key {
        self.0
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
    }
}

impl<Tag, Len, V> DepCombinator for TLVal<Tag, Len, V> where
    Len: AsLen,
    V: DepCombinator<Key = Tag>,
    V::Body: SpecByteLen<T = V::Val>,
 {
    type Key = (Tag, Len);

    type Val = V::Val;

    type Body = ExactLen<V::Body, Len>;

    open spec fn apply(&self, key: Self::Key) -> Self::Body {
        let (tag, len) = key;
        ExactLen(len, self.0.apply(tag))
    }

    open spec fn recover(&self, value: Self::Val) -> Self::Key {
        let tag = self.0.recover(value);
        let body = self.0.apply(tag);
        (tag, Len::from_nat(body.byte_len(value)))
    }

    proof fn lemma_recover_consistent(&self, key: Self::Key, value: Self::Val) {
        if self.apply(key).consistent(value) {
            self.0.lemma_recover_consistent(key.0, value);
            Len::lemma_lossless_casting(key.1);
            let body = self.0.apply(key.0);
            assert(body.byte_len(value) == key.1.as_usize());
            assert(body.byte_len(value) == key.1.as_usize() as nat);
        }
    }
}

} // verus!
