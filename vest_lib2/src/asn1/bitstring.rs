use crate::core::exec::output::*;
use crate::core::exec::{parser::*, serializer::*, ParseError, ParseErrorKind};
use crate::{
    combinators::{
        bytes::ExactLen, length::AsLen, mapped::spec::FnSpecMapper, Bind, Mapped, Pair, Refined,
        Tail, U8,
    },
    core::{proof::*, spec::*},
};
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
use OutputBuf;

verus! {

/// The ASN.1 BIT STRING.
///
/// Represented as:
/// `(number_of_unused_bits_in_final_octet, payload_octets)`.
pub struct BitString<'a, const DER: bool = true> {
    /// Number of unused bits in the final octet of the BIT STRING.
    unused: u8,
    /// The payload octets of the BIT STRING.
    bits: &'a [u8],
}

/// Owned BIT STRING value used when BER segments must be flattened.
#[cfg(feature = "alloc")]
pub struct BitStringOwned {
    unused: u8,
    bits: Vec<u8>,
}

#[verifier::ext_equal]
pub struct BitStringSpec {
    pub unused: u8,
    pub bits: Seq<u8>,
}

impl<'a, const DER: bool> DeepView for BitString<'a, DER> {
    type V = BitStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        BitStringSpec { unused: self.unused, bits: self.bits.deep_view() }
    }
}

#[cfg(feature = "alloc")]
impl DeepView for BitStringOwned {
    type V = BitStringSpec;

    closed spec fn deep_view(&self) -> Self::V {
        BitStringSpec { unused: self.unused, bits: self.bits.deep_view() }
    }
}

impl<'a, const DER: bool> BitString<'a, DER> {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf::<DER>()
    }

    pub fn new(unused: u8, bits: &'a [u8]) -> (bs: Self)
        requires
            unused <= 7,
            bits.len() == 0 ==> unused == 0,
            DER ==> bits.len() > 0 ==> bits@.last().trailing_zeros() >= unused,
        ensures
            (bs.deep_view() == BitStringSpec { unused, bits: bits.deep_view() }),
    {
        BitString { unused, bits }
    }

    pub fn unused(&self) -> u8 {
        self.unused
    }

    pub fn bits(&self) -> &'a [u8] {
        self.bits
    }
}

#[cfg(feature = "alloc")]
impl BitStringOwned {
    #[verifier::type_invariant]
    spec fn wf(&self) -> bool {
        self.deep_view().wf::<false>()
    }

    pub fn new(unused: u8, bits: Vec<u8>) -> (value: Self)
        requires
            unused <= 7,
            bits.len() == 0 ==> unused == 0,
        ensures
            value.deep_view() == (BitStringSpec { unused, bits: bits.deep_view() }),
    {
        Self { unused, bits }
    }

    pub fn unused(&self) -> u8 {
        self.unused
    }

    pub fn bits(&self) -> &[u8] {
        self.bits.as_slice()
    }
}

impl BitStringSpec {
    #[verusfmt::skip]
    pub open spec fn wf<const DER: bool>(&self) -> bool {
        &&& self.unused <= 7
        // 8.6.2.3 If the bitstring is empty, there shall be no subsequent octets, and the initial octet shall be zero.
        &&& (self.bits.len() == 0 ==> self.unused == 0)
        // 11.2.1 Each unused bit in the final octet of the encoding of a bit string value shall be set to zero.
        &&& (DER ==> self.bits.len() > 0 ==> self.bits.last().trailing_zeros() >= self.unused)
    }
}

type BitStringFmt<const DER: bool> = Mapped<
    Refined<Pair<U8, Tail>, PredFnSpec<(u8, Seq<u8>)>>,
    FnSpecMapper<(u8, Seq<u8>), BitStringSpec>,
>;

pub(super) open(super) spec fn bitstring_fmt<const DER: bool>() -> BitStringFmt<DER> {
    Mapped {
        inner: Refined(
            Pair(U8, Tail),
            |r: (u8, Seq<u8>)|
                {
                    let (unused, bits) = r;
                    BitStringSpec { unused, bits }.wf::<DER>()
                },
        ),
        mapper: (
            |r: (u8, Seq<u8>)|
                {
                    let (unused, bits) = r;
                    BitStringSpec { unused, bits }
                },
            |spec: BitStringSpec| (spec.unused, spec.bits),
        ),
    }
}

mod derived_specs {
    use super::*;
    use super::super::BitStringFmt;

    impl<const DER: bool> SpecParser for BitStringFmt<DER> {
        type PVal = BitStringSpec;

        open(super) spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            bitstring_fmt::<DER>().spec_parse(ibuf)
        }
    }

    impl<const DER: bool> Consistency for BitStringFmt<DER> {
        type Val = BitStringSpec;

        open(super) spec fn consistent(&self, v: Self::Val) -> bool {
            bitstring_fmt::<DER>().consistent(v)
        }
    }

    impl<const DER: bool> SpecSerializerDps for BitStringFmt<DER> {
        type SValue = BitStringSpec;

        open(super) spec fn spec_serialize_dps(&self, v: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            bitstring_fmt::<DER>().spec_serialize_dps(v, obuf)
        }
    }

    impl<const DER: bool> SpecSerializer for BitStringFmt<DER> {
        type SVal = BitStringSpec;

        open(super) spec fn spec_serialize(&self, v: Self::SVal) -> Seq<u8> {
            bitstring_fmt::<DER>().spec_serialize(v)
        }
    }

    impl<const DER: bool> SpecByteLen for BitStringFmt<DER> {
        type T = BitStringSpec;

        open(super) spec fn byte_len(&self, v: Self::T) -> nat {
            bitstring_fmt::<DER>().byte_len(v)
        }
    }

}

mod derived_proofs {
    use super::*;
    use super::super::BitStringFmt;

    impl<const DER: bool> SafeParser for BitStringFmt<DER> {
        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            bitstring_fmt::<DER>().lemma_parse_safe(ibuf);
        }
    }

    impl<const DER: bool> Productive for BitStringFmt<DER> {
        proof fn lemma_productive(&self, s: Seq<u8>) {
            bitstring_fmt::<DER>().lemma_productive(s);
        }
    }

    impl<const DER: bool> SoundParser for BitStringFmt<DER> {
        proof fn lemma_parse_sound_consumption(&self, ibuf: Seq<u8>) {
            bitstring_fmt::<DER>().lemma_parse_sound_consumption(ibuf);
        }

        proof fn lemma_parse_sound_value(&self, ibuf: Seq<u8>) {
            bitstring_fmt::<DER>().lemma_parse_sound_value(ibuf);
        }
    }

    impl<const DER: bool> GoodSerializer for BitStringFmt<DER> {
        proof fn lemma_serialize_len(&self, v: Self::SVal) {
            bitstring_fmt::<DER>().lemma_serialize_len(v);
        }
    }

    impl<const DER: bool> SPRoundTripDps for BitStringFmt<DER> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, v: Self::T, obuf: Seq<u8>) {
            bitstring_fmt::<DER>().theorem_serialize_dps_parse_roundtrip(v, obuf);
        }
    }

    impl<const DER: bool> NonMalleable for BitStringFmt<DER> {
        proof fn lemma_parse_non_malleable(&self, buf1: Seq<u8>, buf2: Seq<u8>) {
            bitstring_fmt::<DER>().lemma_parse_non_malleable(buf1, buf2);
        }
    }

    impl<const DER: bool> EquivSerializers for BitStringFmt<DER> {
        proof fn lemma_serialize_equiv_on_empty(&self, v: Self::SVal) {
            bitstring_fmt::<DER>().lemma_serialize_equiv_on_empty(v);
        }
    }

}

impl<'i, const DER: bool> Parser<&'i [u8]> for super::BitStringFmt<DER> {
    type PT = BitString<'i, DER>;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        let (n, (unused, bits)): (usize, (u8, &[u8])) = Pair(U8, Tail).parse(ibuf)?;
        if unused > 7 {
            return Err(ParseError::custom("Invalid number of unused bits in BIT STRING"));
        }
        if bits.len() == 0 && unused != 0 {
            return Err(ParseError::custom("Invalid number of unused bits in BIT STRING"));
        }
        if DER && bits.len() > 0 && bits[bits.len() - 1].trailing_zeros() < unused as u32 {
            return Err(ParseError::custom("Non-canonical encoding of BIT STRING."));
        }
        Ok((n, BitString::new(unused, bits)))
    }
}

impl<Output: OutputBuf, 'i, const DER: bool> Serializer<
    Output,
    BitString<'i, DER>,
> for super::BitStringFmt<DER> {
    fn serialize_into(&self, v: &BitString<'i, DER>, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        U8.serialize_into(&v.unused, obuf);
        Tail.serialize_into(&v.bits, obuf);
    }
}

impl<'i, const DER: bool> Prepare<BitString<'i, DER>> for super::BitStringFmt<DER> {
    fn prepare(&self, v: &BitString<'i, DER>) -> Result<usize, PreSerializeError> {
        proof {
            use_type_invariant(v);
        }
        let n1 = U8.prepare(&v.unused)?;
        let n2 = Tail.prepare(&v.bits)?;
        let total_len = n1.checked_add(n2).ok_or(PreSerializeError::length_too_large())?;
        Ok(total_len)
    }
}

impl<'i, const DER: bool> ByteLen<BitString<'i, DER>> for super::BitStringFmt<DER> {
    fn length(&self, v: &BitString<'i, DER>) -> usize {
        let n1 = U8.length(&v.unused);
        let n2 = Tail.length(&v.bits);
        n1 + n2
    }
}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf> Serializer<Output, BitStringOwned> for super::BitStringFmt<false> {
    fn serialize_into(&self, v: &BitStringOwned, obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

        proof {
            use_type_invariant(v);
        }
        U8.serialize_into(&v.unused, obuf);
        Tail.serialize_into(&v.bits.as_slice(), obuf);
    }
}

#[cfg(feature = "alloc")]
impl Prepare<BitStringOwned> for super::BitStringFmt<false> {
    fn prepare(&self, v: &BitStringOwned) -> Result<usize, PreSerializeError> {
        proof {
            use_type_invariant(v);
        }
        let n1 = U8.prepare(&v.unused)?;
        let n2 = Tail.prepare(&v.bits.as_slice())?;
        n1.checked_add(n2).ok_or(PreSerializeError::length_too_large())
    }
}

#[cfg(feature = "alloc")]
impl ByteLen<BitStringOwned> for super::BitStringFmt<false> {
    fn length(&self, v: &BitStringOwned) -> usize {
        U8.length(&v.unused) + Tail.length(&v.bits.as_slice())
    }
}

} // verus!
