//! Dependent wire fields and inferred values expressed with `Bind` and `Mapped`.
use crate::combinators::{Bind, Choice, Cond, Mapped, Sum, U16Le, U32Le, Varied, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

broadcast use crate::combinators::disjoint::disjointness_lemmas;

proof fn explicit_length_roundtrip() {
    let fmt = Bind(U8, |len: u8| Varied(len));
    let value = (3u8, seq![0xaau8, 0xbbu8, 0xccu8]);
    fmt.theorem_serialize_parse_roundtrip(value);
}

proof fn inferred_length_roundtrip() {
    let fmt = Mapped {
        inner: Bind(U8, |len: u8| Varied(len)),
        mapper: (|wire: (u8, Seq<u8>)| wire.1, |bytes: Seq<u8>| (bytes.len() as u8, bytes)),
    };
    let value = seq![0xaau8, 0xbbu8, 0xccu8];
    assert(fmt.consistent(value));
    assert(fmt.unambiguous());
    fmt.theorem_serialize_parse_roundtrip(value);
    assert(fmt.spec_parse(fmt.spec_serialize(value)) == Some((3int + 1, value)));
}

proof fn explicit_tag_roundtrip() {
    let fmt = Bind(U8, |tag: u8| Choice(Cond(tag == 0u8, U16Le), Cond(tag == 1u8, U32Le)));
    let value = (1u8, Sum::Inr(0x78563412u32));
    assert(fmt.unambiguous());
    fmt.theorem_serialize_parse_roundtrip(value);
}

proof fn inferred_tag_roundtrip() {
    let fmt = Mapped {
        inner: Bind(U8, |tag: u8| Choice(Cond(tag == 0u8, U16Le), Cond(tag == 1u8, U32Le))),
        mapper: (
            |wire: (u8, Sum<u16, u32>)| wire.1,
            |value: Sum<u16, u32>|
                match value {
                    Sum::Inl(v) => (0u8, Sum::Inl(v)),
                    Sum::Inr(v) => (1u8, Sum::Inr(v)),
                },
        ),
    };
    let small = Sum::Inl(0x1234u16);
    let large = Sum::Inr(0x78563412u32);
    assert(fmt.unambiguous());
    assert(fmt.consistent(small) && fmt.consistent(large));
    fmt.theorem_serialize_parse_roundtrip(small);
    fmt.theorem_serialize_parse_roundtrip(large);
}

} // verus!
