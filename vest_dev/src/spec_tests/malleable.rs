use crate::asn1::{BerBool, DerBool};
use crate::combinators::bytes::spec::*;
use crate::combinators::refined::Tag;
use crate::combinators::tuple::Pair;
use crate::combinators::{Fixed, Preceded2, Refined, Terminated2, U16Le, U8};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

// (Non)-malleability Examples
// Helper functions that impose certain trait bounds
proof fn requires_sp_roundtrip<T: SPRoundTrip>(serializer: T, v: T::T, obuf: Seq<u8>)
    requires
        serializer.sp_roundtrip_inv(),
        serializer.consistent(v),
{
    serializer.theorem_serialize_parse_roundtrip(v);
}

proof fn requires_ps_roundtrip<T: PSRoundTrip>(parser: T, ibuf: Seq<u8>)
    requires
        parser.ps_roundtrip_inv(),
{
    parser.theorem_parse_serialize_roundtrip(ibuf);
}

proof fn requires_non_malleable<T: NonMalleable>(parser: T, buf1: Seq<u8>, buf2: Seq<u8>)
    requires
        parser.safe_inv(),
        parser.nonmal_inv(),
{
    parser.lemma_parse_non_malleable(buf1, buf2);
}

proof fn requires_deterministic<T: EquivSerializersGeneral>(
    combinator: T,
    v: <T as SpecSerializer>::SVal,
    obuf: Seq<u8>,
)
    requires
        combinator.equiv_general_inv(),
{
    combinator.lemma_serialize_equiv(v, obuf);
}

// These compositions fail to implement `PSRoundTrip`, `NonMalleable`, or `EquivSerializers`
// traits because they use `Preceded2` or `Terminated2` without `CHECK`, and the discarded
// side does not admit a unique consistent value.
proof fn test_preceded_non_unique_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let val0 = 0u8;
    let val1 = 0u8;
    let parser = Preceded2::<_, _, _, false> { a: U8, b: U8, a_val: 0u8 };
    assert(parser.consistent(val0)) by {
        assert(parser.b.consistent(val0));
    }
    requires_sp_roundtrip(parser, val1, obuf);
    // requires_ps_roundtrip(parser, ibuf, obuf); // Should fail: A does not have AdmitsUniqueVal
}

proof fn test_preceded_non_unique_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Preceded2::<_, _, _, false> { a: U8, b: U8, a_val: 0u8 };
    // requires_non_malleable(parser, buf1, buf2); // Should fail: A does not have AdmitsUniqueVal
}

proof fn test_preceded_non_unique_prefix_deterministic(v: Seq<u8>, obuf: Seq<u8>) {
    let combinator = Preceded2::<_, _, _, false> { a: U8, b: U8, a_val: 0u8 };
    // requires_deterministic(combinator, v, obuf); // Should fail: A does not have AdmitsUniqueVal
}

proof fn test_terminated_non_unique_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = Terminated2::<_, _, _, false> { a: U8, b: U8, b_val: 0u8 };
    // requires_non_malleable(parser, buf1, buf2); // Should fail: B does not have AdmitsUniqueVal
}

proof fn test_terminated_refined_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let refined = Refined { inner: U8, pred: |v: u8| v == 0 };
    let parser = Terminated2::<_, _, _, false> { a: U8, b: refined, b_val: 0u8 };
    // requires_non_malleable(parser, buf1, buf2); // Should fail: Refined does not have AdmitsUniqueVal
}

proof fn test_preceded_terminated_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let inner = Terminated2::<_, _, _, false> { a: U8, b: U8, b_val: 0u8 };
    let outer = Preceded2::<_, _, _, false> { a: U8, b: inner, a_val: 0u8 };
    // requires_non_malleable(outer, buf1, buf2); // Should fail: multiple sources of non-uniqueness
    let val1 = 0u8;
    let val2 = 0u8;
    assert(inner.b.consistent(0u8));
    assert(outer.a.consistent(0u8));
    assert(outer.consistent(val1));
    assert(outer.consistent(val2));
    let obuf = Seq::empty();
    let v = 0u8;
    requires_sp_roundtrip(outer, v, obuf);
}

// Tag has AdmitsUniqueVal because it restricts
// its consistent values to exactly one value (the tag).
proof fn test_preceded_tag_prefix_ps(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let tag = Tag { inner: U8, tag: 0u8 };
    let combinator = Preceded2::<_, _, _, false> { a: tag, b: U8, a_val: 0u8 };
    assert(combinator.ps_roundtrip_inv()) by {
    }
    combinator.theorem_parse_serialize_roundtrip(ibuf);  // Should pass: Tag has AdmitsUniqueVal
}

proof fn test_preceded_tag_prefix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: U8, tag: 0u8 };
    let parser = Preceded2::<_, _, _, false> { a: tag, b: U8, a_val: 0u8 };
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has AdmitsUniqueVal
}

proof fn test_preceded_tag_prefix_deterministic(v: u8, obuf: Seq<u8>) {
    let val = 0u8;
    let tag = Tag { inner: U8, tag: val };
    let serializer = Preceded2::<_, _, _, false> { a: tag, b: U8, a_val: val };

    assert(serializer.unambiguous()) by {
        unambiguous_pair(Pair(tag, U8));
    }
    requires_deterministic(serializer, v, obuf);  // Should pass: Tag has AdmitsUniqueVal
}

proof fn test_terminated_tag_suffix_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag = Tag { inner: U8, tag: 0xFFu8 };
    let parser = Terminated2::<_, _, _, false> { a: U8, b: tag, b_val: 0xFFu8 };
    requires_non_malleable(parser, buf1, buf2);  // Should pass: Tag has AdmitsUniqueVal
}

proof fn test_mixed_preceded_terminated_with_tag_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let tag1 = Tag { inner: U8, tag: 0x01u8 };
    let tag2 = Tag { inner: U8, tag: 0x02u8 };
    let inner = Terminated2::<_, _, _, false> { a: U8, b: tag1, b_val: 0x01u8 };
    let outer = Preceded2::<_, _, _, false> { a: tag2, b: inner, a_val: 0x02u8 };
    requires_non_malleable(outer, buf1, buf2);  // Should pass: both Tags have AdmitsUniqueVal
}

proof fn test_double_terminated_tag_deterministic(v: u8)
// requires
//     v.len() == 2,
{
    let val1 = 0x00u8;
    let val2 = 0xFFu8;
    let obuf = Seq::empty();
    let tag1_bytes = [val1, val1];
    let tag2_bytes = [val2, val2];
    let tag1 = Tag { inner: Fixed::<2>, tag: tag1_bytes };
    let tag2 = Tag { inner: Fixed::<2>, tag: tag2_bytes };
    let inner =
        Terminated2::<_, _, _, false> { a: U8, b: tag1, b_val: tag1_bytes };
    let outer =
        Terminated2::<_, _, _, false> { a: inner, b: tag2, b_val: tag2_bytes };

    let footer_buf = tag2.spec_serialize_dps(seq![val2, val2], obuf);
    let inner_buf = tag1.spec_serialize_dps(seq![val1, val1], footer_buf);

    assert(inner.unambiguous());
    assert(outer.unambiguous());
    requires_deterministic(outer, v, obuf);  // Should pass: both Tags have AdmitsUniqueVal
}

// BerBool: Malleable Boolean Combinator Tests
proof fn test_berbool_sp_roundtrip(v: bool, obuf: Seq<u8>) {
    let combinator = BerBool;
    requires_sp_roundtrip(combinator, v, obuf);  // Should pass: BerBool implements SPRoundTrip
}

proof fn test_berbool_fails_ps_roundtrip(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let parser = BerBool;
    // requires_ps_roundtrip(parser, ibuf); // Would fail: BerBool does not implement PSRoundTrip
}

proof fn test_berbool_fails_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = BerBool;
    // requires_non_malleable(parser, buf1, buf2); // Would fail: BerBool does not implement NonMalleable
}

proof fn test_derbool_ps_roundtrip(ibuf: Seq<u8>, obuf: Seq<u8>) {
    let parser = DerBool;
    requires_ps_roundtrip(parser, ibuf);
}

proof fn test_derbool_non_malleable(buf1: Seq<u8>, buf2: Seq<u8>) {
    let parser = DerBool;
    requires_non_malleable(parser, buf1, buf2);
}

proof fn unambiguous_pair<A: SPRoundTripDps + NonTailFmt, B: SPRoundTripDps>(pair: Pair<A, B>)
    requires
        pair.0.serialize_dps_inv(),
        pair.0.unambiguous(),
        pair.1.unambiguous(),
    ensures
        pair.unambiguous(),
{
}

proof fn test_large_format_with_berbools() {
    // Format: [Header 0xAA] [(BerBool, BerBool, Fixed::<2>)] [Footer 0xFF]
    let header = 0xAAu8;
    let format_inner = Pair(Pair(BerBool, BerBool), Fixed::<2>);
    let format = Terminated2::<_, _, _, false> {
        a: Preceded2::<_, _, _, false> {
            a: Tag { inner: U8, tag: header },
            b: format_inner,
            a_val: header,
        },
        b: Tag { inner: U8, tag: 0xFFu8 },
        b_val: 0xFFu8,
    };

    let v = ((true, false), seq![0x11u8, 0x22u8]);
    let obuf = Seq::empty();

    assert(format.a.a.unambiguous());
    assert(format.a.b.unambiguous());

    assert(format.a.unambiguous()) by {
        unambiguous_pair(Pair(format.a.a, format.a.b));
    }
    assert(format.unambiguous()) by {
        unambiguous_pair(Pair(format.a, format.b));
    }
    assert(format.a.a.consistent(header));
    assert(format.b.consistent(0xFFu8));
    assert(format.consistent(v)) by {
    }
    requires_sp_roundtrip(format, v, obuf);
    // requires_non_malleable(format, header_val, footer_val); // Should fail: BerBool is malleable

    // But multiple different buffers parse to the same value
    // [0xAA] [0x01] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x01
    // [0xAA] [0xFF] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0xFF
    // [0xAA] [0x42] [0x00] [0x11, 0x22] [0xFF] - true encoded as 0x42

    let buf1 = seq![0xAAu8, 0x01u8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];
    let buf2 = seq![0xAAu8, 0xFFu8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];
    let buf3 = seq![0xAAu8, 0x42u8, 0x00u8, 0x11u8, 0x22u8, 0xFFu8];

    if let Some((n1, v1)) = format.spec_parse(buf1) {
        if let Some((n2, v2)) = format.spec_parse(buf2) {
            if let Some((n3, v3)) = format.spec_parse(buf3) {
                assert(v1 == v);
                assert(v2 == v);
                assert(v3 == v);
                assert(n1 == n2 == n3);

                // But all byte prefixes are different
                assert(buf1.take(n1)[1] == 0x01u8);
                assert(buf2.take(n2)[1] == 0xFFu8);
                assert(buf3.take(n3)[1] == 0x42u8);
            }
        }
    }
}

} // verus!
