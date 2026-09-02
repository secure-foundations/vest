use crate::asn1::BerBoolFmt;
use crate::combinators::{
    Bind, Choice, Eof, Pair, PrefixTagged, Repeat, RepeatTillEnd, Star, Sum, U16Le, Varied, U8,
};
use crate::core::spec::*;
use vstd::prelude::*;
use PrefixTagged as Tagged;

verus! {

type DemoFmt1 = Pair<BerBoolFmt, Choice<Tagged<U8, u8, U16Le>, RepeatTillEnd<U16Le>>>;

type DemoFmt2 = Pair<
    BerBoolFmt,
    Choice<Tagged<U8, u8, U16Le>, RepeatTillEnd<Bind<U16Le, spec_fn(u16) -> Varied<u16>>>>,
>;



proof fn test_value_byte_len_demo() {
    let fmt: DemoFmt1 = Pair(BerBoolFmt, Choice(Tagged(U8, 0xA5u8, U16Le), RepeatTillEnd(U16Le)));
    let fmt2: DemoFmt2 = Pair(
        BerBoolFmt,
        Choice(Tagged(U8, 0xA5u8, U16Le), RepeatTillEnd(Bind(U16Le, |x| Varied(x)))),
    );

    reveal(<Star::<_> as Consistency>::consistent);
    reveal(<Star::<_> as SpecByteLen>::byte_len);

    let tagged_v = (false, Sum::Inl(0x3456u16));
    let repeated_v = (true, Sum::Inr(seq![0x1111u16, 0x2222u16, 0x3333u16, 0x4444u16, 0x5555u16]));
    let repeated_v2 = (
        true,
        Sum::Inr(
            seq![
                (0x01u16, seq![0x00u8]),
                (0x02u16, seq![0x00u8, 0x01u8]),
                (0x03u16, seq![0x00u8, 0x01u8, 0x02u8]),
            ],
        ),
    );

    fmt.lemma_value_len_matches_byte_len(tagged_v);
    fmt.lemma_value_len_matches_byte_len(repeated_v);
    fmt2.lemma_value_len_matches_byte_len(repeated_v2);

    assert(DemoFmt1::value_byte_len(tagged_v) == 4);
    assert(fmt.byte_len(tagged_v) == 4);

    assert(Star::<U16Le>::value_byte_len(
        seq![0x1111u16, 0x2222u16, 0x3333u16, 0x4444u16, 0x5555u16],
    ) == 10) by (compute);
    assert(DemoFmt1::value_byte_len(repeated_v) == 11);
    assert(Star::<Bind<U16Le, spec_fn(u16) -> Varied<u16>>>::value_byte_len(
        seq![
            (0x01u16, seq![0x00u8]),
            (0x02u16, seq![0x00u8, 0x01u8]),
            (0x03u16, seq![0x00u8, 0x01u8, 0x02u8]),
        ],
    ) == 12) by (compute);
    assert(DemoFmt2::value_byte_len(repeated_v2) == 13);
    assert(fmt.byte_len(repeated_v) == 11);
}

} // verus!
