use crate::combinators::tail::PairRev;
use crate::combinators::{Eof, ExactLen, Repeat, Star};
use crate::leb128::*;
use crate::{
    combinators::{
        implicit::KVFormat, mapped::spec::*, recursive::*, Alt, FixWith, Implicit, Mapped, Pair,
        Refined, Sum, U8,
    },
    core::{proof::*, spec::*},
};
use vstd::arithmetic::{div_mod::*, power::*, power2::*};
use vstd::prelude::*;

verus! {

pub type Base128Fmt<const MINIMAL: bool> = Mapped<Base128WireFmt<MINIMAL>, NatFromToBE128<MINIMAL>>;

pub type Base128WireFmt<const MINIMAL: bool> = Mapped<
    Refined<Repeat<ContinuationByte, TerminalByte>, PredFnSpec<(Seq<u8>, u8)>>,
    BiMap<spec_fn((Seq<u8>, u8)) -> Seq<u8>, SplitSeqAtLast>,
>;

pub open spec fn base128_fmt<const MINIMAL: bool>() -> Base128Fmt<MINIMAL> {
    Mapped { inner: base128_wire_fmt::<MINIMAL>(), mapper: NatFromToBE128::<MINIMAL> }
}

pub open spec fn base128_wire_fmt<const MINIMAL: bool>() -> Base128WireFmt<MINIMAL> {
    Mapped {
        inner: Refined(
            Repeat(continuation_byte(), terminal_byte()),
            // No leading zeros allowed if MINIMAL
            |pair: (Seq<u8>, u8)| MINIMAL ==> (pair.0.len() > 0 ==> pair.0[0] != 0),
        ),
        mapper: BiMap(|pair: (Seq<u8>, u8)| pair.0.push(pair.1), SplitSeqAtLast),
    }
}

pub struct SplitSeqAtLast;

impl SpecMap for SplitSeqAtLast {
    type Input = Seq<u8>;

    type Output = (Seq<u8>, u8);

    open spec fn wf(&self, s: Self::Input) -> bool {
        s.len() > 0
    }

    open spec fn spec_map(&self, i: Self::Input) -> Self::Output {
        (i.drop_last(), i.last())
    }
}

pub struct NatFromToBE128<const MINIMAL: bool>;

impl<const MINIMAL: bool> SpecMapper for NatFromToBE128<MINIMAL> {
    type In = Seq<u8>;

    type Out = nat;

    open spec fn wf_in(&self, bytes: Self::In) -> bool {
        &&& forall|i: int| 0 <= i < bytes.len() ==> bytes[i] < 128
        &&& bytes.len() > 0
        &&& MINIMAL ==> (bytes.len() > 1 ==> bytes[0] != 0)
    }

    open spec fn spec_map(&self, bytes: Self::In) -> Self::Out {
        nat_from_base128(bytes)
    }

    open spec fn spec_map_rev(&self, v: Self::Out) -> Self::In {
        nat_to_base128(v)
    }
}

impl<const MINIMAL: bool> LossyMapper for NatFromToBE128<MINIMAL> {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        lemma_to_from_base128_roundtrip(o);
    }

    proof fn lemma_mapper_wf_out_in(&self, o: Self::Out) {
        lemma_nat_to_base128_props(o);
    }
}

impl LosslessMapper for NatFromToBE128<true> {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        lemma_from_to_base128_roundtrip(i);
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

/// Unsigned big-endian base-128 decoding.
pub open spec fn nat_from_base128(bytes: Seq<u8>) -> nat
    recommends
        forall|i: int| 0 <= i < bytes.len() ==> bytes[i] < 128,
    decreases bytes.len(),
{
    if bytes.len() == 0 {
        0
    } else {
        nat_from_base128(bytes.drop_last()) * 128 + bytes.last() as nat
    }
}

/// Unsigned big-endian base-128 encoding.
pub open spec fn nat_to_base128(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 128 {
        seq![n as u8]
    } else {
        nat_to_base128((n / 128) as nat).push((n % 128) as u8)
    }
}

pub proof fn lemma_nat_from_base128_push(bytes: Seq<u8>, b: u8)
    ensures
        nat_from_base128(bytes.push(b)) == nat_from_base128(bytes) * 128 + b as nat,
{
    assert(bytes.push(b).drop_last() == bytes);
}

pub proof fn lemma_to_from_base128_roundtrip(n: nat)
    ensures
        nat_from_base128(nat_to_base128(n)) == n,
    decreases n,
{
    if n < 128 {
        lemma_nat_from_base128_push(seq![], n as u8);
    } else {
        let q = (n / 128) as nat;
        let r = (n % 128) as nat;
        lemma_to_from_base128_roundtrip(q);
        lemma_nat_from_base128_push(nat_to_base128(q), r as u8);
    }
}

pub proof fn lemma_from_to_base128_roundtrip(bytes: Seq<u8>)
    requires
        forall|i: int| 0 <= i < bytes.len() ==> bytes[i] < 128,
        bytes.len() > 0,
        bytes.len() > 1 ==> bytes[0] != 0,
    ensures
        nat_to_base128(nat_from_base128(bytes)) == bytes,
    decreases bytes.len(),
{
    if bytes.len() == 1 {
        lemma_nat_from_base128_push(seq![], bytes[0]);
        assert(bytes == seq![bytes[0]]);
    } else {
        let prefix = bytes.drop_last();
        lemma_from_to_base128_roundtrip(prefix);
    }
}

pub proof fn lemma_nat_to_base128_props(n: nat)
    ensures
        nat_to_base128(n).len() > 0,
        n > 0 ==> nat_to_base128(n)[0] != 0,
        forall|i: int| 0 <= i < nat_to_base128(n).len() ==> nat_to_base128(n)[i] < 128,
    decreases n,
{
    if n < 128 {
    } else {
        let q = (n / 128) as nat;
        lemma_nat_to_base128_props(q);
    }
}

pub broadcast proof fn lemma_base128_wire_fmt_props<const MINIMAL: bool>(bytes: Seq<u8>)
    requires
        #[trigger] base128_wire_fmt::<MINIMAL>().consistent(bytes),
    ensures
        #[trigger] NatFromToBE128::<MINIMAL>.wf_in(bytes),
{
    let pair = SplitSeqAtLast.spec_map(bytes);

    assert forall|i: int| 0 <= i < bytes.len() implies bytes[i] < 128 by {
        if i < bytes.len() - 1 {
            assert(pair.0[i] < 128);
        } else {
            assert(pair.1 < 128);
        }
    }
}

pub struct Base128<const MINIMAL: bool>;

impl<const MINIMAL: bool> SpecParser for Base128<MINIMAL> {
    type PVal = nat;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        base128_fmt::<MINIMAL>().spec_parse(ibuf)
    }
}

impl<const MINIMAL: bool> Consistency for Base128<MINIMAL> {
    type Val = nat;

    open spec fn consistent(&self, v: Self::Val) -> bool {
        base128_fmt::<MINIMAL>().consistent(v)
    }
}

impl<const MINIMAL: bool> SafeParser for Base128<MINIMAL> {
    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        base128_fmt::<MINIMAL>().lemma_parse_safe(ibuf);
    }
}

impl SoundParser for Base128<true> {
    proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
        broadcast use lemma_base128_wire_fmt_props;

        assert forall|s: Seq<u8>, b: u8| #[trigger] s.push(b).drop_last() == s by {}
        assert(base128_fmt::<true>().sound_inv());
        base128_fmt::<true>().lemma_parse_sound_consumption(ibuf);
    }

    proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
        broadcast use lemma_base128_wire_fmt_props;

        assert forall|s: Seq<u8>, b: u8| #[trigger] s.push(b).drop_last() == s by {}
        assert(base128_fmt::<true>().sound_inv());
        base128_fmt::<true>().lemma_parse_sound_value(ibuf);
    }
}

impl<const MINIMAL: bool> SpecSerializerDps for Base128<MINIMAL> {
    type SValue = nat;

    open spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        base128_fmt::<MINIMAL>().spec_serialize_dps(v, obuf)
    }
}

impl<const MINIMAL: bool> SpecSerializer for Base128<MINIMAL> {
    type SVal = nat;

    open spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
        base128_fmt::<MINIMAL>().spec_serialize(v)
    }
}

impl<const MINIMAL: bool> NonTailFmt for Base128<MINIMAL> {
    proof fn lemma_serialize_dps_prepend(&self, v: Self::SValue, obuf: Seq<u8>) {
        base128_fmt::<MINIMAL>().lemma_serialize_dps_prepend(v, obuf);
    }

    proof fn lemma_serialize_dps_len(&self, v: Self::SValue, obuf: Seq<u8>) {
        base128_fmt::<MINIMAL>().lemma_serialize_dps_len(v, obuf);
    }
}

impl<const MINIMAL: bool> GoodSerializer for Base128<MINIMAL> {
    proof fn lemma_serialize_len(&self, v: Self::SVal) {
        base128_fmt::<MINIMAL>().lemma_serialize_len(v);
    }
}

impl<const MINIMAL: bool> SpecByteLen for Base128<MINIMAL> {
    type T = nat;

    open spec fn byte_len(&self, v: Self::T) -> nat {
        base128_fmt::<MINIMAL>().byte_len(v)
    }
}

impl<const MINIMAL: bool> SPRoundTripDps for Base128<MINIMAL> {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
        assert forall|s: Seq<u8>| #![auto] s.len() > 0 ==> s.drop_last().push(s.last()) == s by {}
        assert(base128_fmt::<MINIMAL>().inner.unambiguous());
        base128_fmt::<MINIMAL>().theorem_serialize_dps_parse_roundtrip(v, obuf);
    }
}

impl<const MINIMAL: bool> NoLookAhead for Base128<MINIMAL> {
    proof fn lemma_no_lookahead(&self, i1: Seq<u8>, i2: Seq<u8>) {
        base128_fmt::<MINIMAL>().lemma_no_lookahead(i1, i2);
    }
}

impl NonMalleable for Base128<true> {
    proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
        broadcast use lemma_base128_wire_fmt_props;

        assert forall|s: Seq<u8>, b: u8| #[trigger] s.push(b).drop_last() == s by {}
        assert(base128_fmt::<true>().nonmal_inv());
        base128_fmt::<true>().lemma_parse_non_malleable(buf1, buf2);
    }
}

impl<const MINIMAL: bool> EquivSerializersGeneral for Base128<MINIMAL> {
    proof fn lemma_serialize_equiv(&self, v: Self::SVal, obuf: Seq<u8>) {
        base128_fmt::<MINIMAL>().lemma_serialize_equiv(v, obuf);
    }
}

impl<const MINIMAL: bool> EquivSerializers for Base128<MINIMAL> {
    proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
        base128_fmt::<MINIMAL>().lemma_serialize_equiv_on_empty(v);
    }
}

// pub struct Base128RecBody;
// impl SpecRecBody for Base128RecBody {
//     type Param = usize;
//     type T = nat;
//     type Body = ExactLen<
//         Alt<
//             Mapped<Eof, BiMapper<(), nat>>,
//             Mapped<PairRev<BundledSpecs<nat>, U8>, BiMapper<(nat, u8), nat>>,
//         >,
//         usize,
//     >;
//     open spec fn spec_body(
//         full_len: Self::Param,
//         rec: ParamRecSpecs<Self::Param, Self::T>,
//     ) -> Self::Body {
//         ExactLen(
//             full_len,
//             Alt(
//                 Mapped { inner: Eof, mapper: BiMap(|_eof: ()| 0nat, |_n: nat| ()) },
//                 Mapped {
//                     inner: PairRev(U8, rec((full_len - 1) as usize)),
//                     // map: (lsb, rest) -> lsb | (rest << 7)
//                     // map_rev: o -> (lsb = o & 0x7F, rest = o >> 7)
//                     mapper: BiMap(
//                         |pair: (nat, u8)| 128 * pair.0 + pair.1 as nat,
//                         |o: nat| (o / 128, (o % 128) as u8),
//                     ),
//                 },
//             ),
//         )
//     }
// }
// pub struct Base128RecBody;
// impl SpecRecBody for Base128RecBody {
//     type Param = nat;
//     type T = nat;
//     type Body = Alt<
//         Mapped<Refined<U8, PredFnSpec<u8>>, BiMapper<u8, nat>>,
//         Implicit<ContinuationByte, KVFormat<u8, nat, BundledSpecs<nat>>>,
//     >;
//     /// vN(A) ::= n:byte            => A * 2^7 + n                                       if n < 2^7
//     ///
//     ///          |  n:byte  m:v(N-7)(A * 2^7 + (n - 2^7))  => m                            if n >= 2^7
//     open spec fn spec_body(
//         acc: Self::Param,
//         rec: ParamRecSpecs<Self::Param, Self::T>,
//     ) -> Self::Body {
//         Alt(
//             Mapped {
//                 inner: Refined(U8, |b: u8| b < CONTINUATION_BIT),
//                 mapper: BiMap(|b: u8| acc * 128 + b as nat, |n: nat| (n - acc * 128) as u8),
//             },
//             Implicit(
//                 continuation_byte(),
//                 (|b: u8| rec(acc * 128 + b as nat), |n: nat| (n - acc * 128) as u8),
//             ),
//         // Mapped {
//         //     inner: Bind(continuation_byte(), |b: u8| rec(acc * 128 + b as nat)),
//         //     mapper: BiMap(|pair: (u8, nat)| pair.1, |n: nat| -> (u8, nat) {
//         //     }
//         // }
//         )
//     }
// }
} // verus!
