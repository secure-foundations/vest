//! BER SEQUENCE framing and schema-body termination.
//!
//! `BerSeqBody` replaces a field chain's final EOF with a consuming EOC for
//! indefinite framing. Complete child TLVs are unchanged. EXPLICIT wrappers
//! reuse the same framing through `BerSequenceFmt`.
use crate::asn1::{ASN1Fmt, BerLength, BerLengthFmt, Class, DefaultedFmt, Tag, TagFmt, BER};
use crate::combinators::{
    bytes::ExactLen, mapped::spec::FnSpecMapper, Bind, Const, Eof, Mapped, Optional, Pair,
    PrefixTagged, SuffixTagged, Sum,
};
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::{
    ByteLen, OutputBuf, PResult, Parser, PreSerializeError, Prepare, Serializer,
};
use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

use super::eoc::{EocEndFmt, EOC_END};
use Sum::Inl as L;
use Sum::Inr as R;

verus! {

/// An EOF-terminated body for BER SEQUENCE and EXPLICIT wrappers.
///
/// Indefinite framing replaces the final [`Eof`] with [`EOC_END`], consuming the
/// marker without changing the body's value type.
/// Only the continuation is changed; complete child TLVs are left intact.
/// Implementations follow `Pair`, `Optional`, and `DefaultedFmt` continuations;
/// `SuffixTagged<C, Eof, ()>` provides the same transformation for EXPLICIT wrappers.
pub trait BerSeqBody: SpecCombinator + Copy {
    type WithEoc: SpecCombinator<T = Self::T> + Copy;

    spec fn spec_with_eoc(&self) -> Self::WithEoc;

    fn with_eoc(&self) -> (body: Self::WithEoc)
        ensures
            body == self.spec_with_eoc(),
    ;

    proof fn lemma_eoc_consistent(&self, value: Self::T)
        ensures
            self.spec_with_eoc().consistent(value) == self.consistent(value),
    ;

    proof fn lemma_eoc_serialize(&self, value: Self::T)
        ensures
            self.spec_with_eoc().spec_serialize(value) == self.spec_serialize(value)
                + EOC_END.spec_serialize(()),
    ;

    proof fn lemma_eoc_len(&self, value: Self::T)
        ensures
            self.spec_with_eoc().byte_len(value) == self.byte_len(value) + 2,
    ;
}

impl BerSeqBody for Eof {
    type WithEoc = EocEndFmt;

    open spec fn spec_with_eoc(&self) -> Self::WithEoc {
        EOC_END
    }

    fn with_eoc(&self) -> Self::WithEoc {
        EOC_END
    }

    proof fn lemma_eoc_consistent(&self, value: ()) {
    }

    proof fn lemma_eoc_serialize(&self, value: ()) {
    }

    proof fn lemma_eoc_len(&self, value: ()) {
    }
}

impl<A: SpecCombinator + Copy, B: BerSeqBody> BerSeqBody for Pair<A, B> {
    type WithEoc = Pair<A, B::WithEoc>;

    open spec fn spec_with_eoc(&self) -> Self::WithEoc {
        Pair(self.0, self.1.spec_with_eoc())
    }

    fn with_eoc(&self) -> Self::WithEoc {
        Pair(self.0, self.1.with_eoc())
    }

    proof fn lemma_eoc_consistent(&self, value: Self::T) {
        self.1.lemma_eoc_consistent(value.1);
    }

    proof fn lemma_eoc_serialize(&self, value: Self::T) {
        self.1.lemma_eoc_serialize(value.1);
    }

    proof fn lemma_eoc_len(&self, value: Self::T) {
        self.1.lemma_eoc_len(value.1);
    }
}

impl<A: SpecCombinator + Copy, B: BerSeqBody> BerSeqBody for Optional<A, B> {
    type WithEoc = Optional<A, B::WithEoc>;

    open spec fn spec_with_eoc(&self) -> Self::WithEoc {
        Optional(self.0, self.1.spec_with_eoc())
    }

    fn with_eoc(&self) -> Self::WithEoc {
        Optional(self.0, self.1.with_eoc())
    }

    proof fn lemma_eoc_consistent(&self, value: Self::T) {
        self.1.lemma_eoc_consistent(value.1);
    }

    proof fn lemma_eoc_serialize(&self, value: Self::T) {
        self.1.lemma_eoc_serialize(value.1);
    }

    proof fn lemma_eoc_len(&self, value: Self::T) {
        self.1.lemma_eoc_len(value.1);
    }
}

impl<F, R, const DER: bool> BerSeqBody for DefaultedFmt<F, F::T, R, DER> where
    F: SpecCombinator + Copy,
    F::T: Copy,
    R: BerSeqBody,
 {
    type WithEoc = DefaultedFmt<F, F::T, R::WithEoc, DER>;

    open spec fn spec_with_eoc(&self) -> Self::WithEoc {
        DefaultedFmt(self.0, self.1, self.2.spec_with_eoc())
    }

    fn with_eoc(&self) -> Self::WithEoc {
        DefaultedFmt(self.0, self.1, self.2.with_eoc())
    }

    proof fn lemma_eoc_consistent(&self, value: Self::T) {
        self.2.lemma_eoc_consistent(value.1);
    }

    proof fn lemma_eoc_serialize(&self, value: Self::T) {
        self.2.lemma_eoc_serialize(value.1);
    }

    proof fn lemma_eoc_len(&self, value: Self::T) {
        self.2.lemma_eoc_len(value.1);
    }
}

impl<C: SpecCombinator + Copy> BerSeqBody for SuffixTagged<C, Eof, ()> where (): Copy {
    type WithEoc = SuffixTagged<C, EocEndFmt, ()>;

    open spec fn spec_with_eoc(&self) -> Self::WithEoc {
        SuffixTagged(self.0, EOC_END, ())
    }

    fn with_eoc(&self) -> Self::WithEoc {
        SuffixTagged(self.0, EOC_END, ())
    }

    proof fn lemma_eoc_consistent(&self, value: Self::T) {
    }

    proof fn lemma_eoc_serialize(&self, value: Self::T) {
    }

    proof fn lemma_eoc_len(&self, value: Self::T) {
    }
}

type BerSequenceWireType<T> = (BerLength, Sum<T, T>);

type BerSequenceFmt__<C> = Mapped<
    PrefixTagged<
        TagFmt,
        Tag,
        Bind<
            BerLengthFmt,
            spec_fn(BerLength) -> Sum<ExactLen<C, usize>, <C as BerSeqBody>::WithEoc>,
        >,
    >,
    FnSpecMapper<BerSequenceWireType<<C as SpecByteLen>::T>, <C as SpecByteLen>::T>,
>;

/// BER `SEQUENCE` accepting definite and indefinite outer length forms.
///
/// The body ends in `Eof`. For indefinite framing, [`BerSeqBody`] replaces that terminal with
/// an EOC terminal. Normalization uses definite framing when the content length fits
/// `usize`, and indefinite framing for larger mathematical values.
pub open spec fn ber_sequence_fmt<C: BerSeqBody>(tag: Tag, content: C) -> BerSequenceFmt__<C> {
    #[verusfmt::skip]
    Mapped {
        inner: PrefixTagged(TagFmt, tag, Bind(BerLengthFmt, |len: BerLength|
                match len {
                    BerLength::Definite(len) => L(ExactLen(len, content)),
                    BerLength::Indefinite => R(content.spec_with_eoc()),
                },
            ),
        ),
        mapper: (
            |parsed: BerSequenceWireType<C::T>|
                match parsed.1 {
                    L(value) => value,
                    R(value) => value,
                },
            |value: C::T| {
                let len = content.byte_len(value);
                if len <= usize::MAX {
                    (BerLength::Definite(len as usize), L(value))
                } else {
                    (BerLength::Indefinite, R(value))
                }
            },
        ),
    }
}

pub(crate) proof fn lemma_ber_sequence_consistent<C: BerSeqBody>(tag: Tag, content: C, value: C::T)
    ensures
        content.spec_with_eoc().consistent(value) == content.consistent(value),
        BerSequenceFmt(tag, content).consistent(value) == (TagFmt.consistent(tag)
            && content.consistent(value)),
{
    content.lemma_eoc_consistent(value);
    crate::asn1::length::lemma_length_fmt_consistent::<BER>(content.byte_len(value) as usize);
}

proof fn lemma_content_len<C: BerSeqBody>(tag: Tag, content: C, value: C::T)
    ensures
        content.byte_len(value) <= BerSequenceFmt(tag, content).byte_len(value),
{
    content.lemma_eoc_len(value);
}

proof fn lemma_definite<C: BerSeqBody>(tag: Tag, content: C, value: C::T)
    requires
        content.byte_len(value) <= usize::MAX,
    ensures
        BerSequenceFmt(tag, content).consistent(value) == ASN1Fmt::<_, BER>(
            tag,
            content,
        ).consistent(value),
        BerSequenceFmt(tag, content).byte_len(value) == ASN1Fmt::<_, BER>(tag, content).byte_len(
            value,
        ),
        BerSequenceFmt(tag, content).spec_serialize(value) == ASN1Fmt::<_, BER>(
            tag,
            content,
        ).spec_serialize(value),
        forall|suffix: Seq<u8>| #[trigger]
            BerSequenceFmt(tag, content).spec_serialize_dps(value, suffix) == ASN1Fmt::<_, BER>(
                tag,
                content,
            ).spec_serialize_dps(value, suffix),
{
}

/// BER `SEQUENCE` codec with a configurable outer tag.
///
/// Parsing accepts definite and indefinite framing for one schema body. Serialization always
/// emits definite-length BER for executable-sized output buffers.
#[derive(Copy)]
pub struct BerSequenceFmt<C>(pub Tag, pub C);

impl<C: BerSeqBody> BerSequenceFmt<C> {
    /// The same schema fields with a consuming EOC terminal.
    pub open spec fn eoc_body(&self) -> C::WithEoc {
        self.1.spec_with_eoc()
    }
}

impl<C: Clone> Clone for BerSequenceFmt<C> {
    fn clone(&self) -> (cloned: Self)
        ensures
            cloned.0 == self.0,
            call_ensures(C::clone, (&self.1,), cloned.1),
    {
        BerSequenceFmt(self.0, self.1.clone())
    }
}

impl<C: Copy> BerSequenceFmt<C> {
    /// Ordinary universal `SEQUENCE`.
    #[verifier::allow_in_spec]
    pub const fn universal(content: C) -> Self
        returns
            Self(TagFmt::SEQUENCE, content),
    {
        Self(TagFmt::SEQUENCE, content)
    }

    /// An IMPLICIT-tagged `SEQUENCE`.
    #[verifier::allow_in_spec]
    pub const fn implicit(class: Class, number: u64, content: C) -> Self
        returns
            Self(
                Tag {
                    class,
                    constructed: true,
                    number: crate::asn1::tag::tag_num_from_uint(number),
                },
                content,
            ),
    {
        Self(
            Tag { class, constructed: true, number: crate::asn1::tag::tag_num_from_uint(number) },
            content,
        )
    }
}

mod derived_specs {
    use super::*;

    impl<C: BerSeqBody> SpecParser for BerSequenceFmt<C> {
        type PVal = C::T;

        open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
            ber_sequence_fmt(self.0, self.1).spec_parse(ibuf)
        }
    }

    impl<C: BerSeqBody> Consistency for BerSequenceFmt<C> {
        type Val = C::T;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            ber_sequence_fmt(self.0, self.1).consistent(value)
        }
    }

    impl<C: BerSeqBody> SpecSerializerDps for BerSequenceFmt<C> {
        type SValue = C::T;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            ber_sequence_fmt(self.0, self.1).spec_serialize_dps(value, obuf)
        }
    }

    impl<C: BerSeqBody> SpecSerializer for BerSequenceFmt<C> {
        type SVal = C::T;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            ber_sequence_fmt(self.0, self.1).spec_serialize(value)
        }
    }

    impl<C: BerSeqBody> SpecByteLen for BerSequenceFmt<C> {
        type T = C::T;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            ber_sequence_fmt(self.0, self.1).byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<C: BerSeqBody + SafeParser> SafeParser for BerSequenceFmt<C> where C::WithEoc: SafeParser {
        open spec fn safe_inv(&self) -> bool {
            self.1.safe_inv() && self.1.spec_with_eoc().safe_inv()
        }

        proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_parse_safe(ibuf);
        }
    }

    impl<C: BerSeqBody + Productive> Productive for BerSequenceFmt<C> where C::WithEoc: Productive {
        open spec fn productive_inv(&self) -> bool {
            self.safe_inv()
        }

        proof fn lemma_productive(&self, ibuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_productive(ibuf);
        }
    }

    impl<C: BerSeqBody + SoundParser> SoundParser for BerSequenceFmt<C> where
        C::WithEoc: SoundParser,
     {
        open spec fn sound_inv(&self) -> bool {
            self.1.sound_inv() && self.1.spec_with_eoc().sound_inv()
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            let fmt = ber_sequence_fmt(self.0, self.1);
            TagFmt.lemma_parse_sound_value(input);
            if let Some((_, (length, branch))) = fmt.inner.spec_parse(input) {
                TagFmt.lemma_parse_safe(input);
                let after_tag = input[(TagFmt.spec_parse(input)->0).0..];
                BerLengthFmt.lemma_parse_safe(after_tag);
                let bytes = after_tag[(BerLengthFmt.spec_parse(after_tag)->0).0..];
                match length {
                    BerLength::Definite(len) => self.1.lemma_parse_sound_value(bytes[0..len]),
                    BerLength::Indefinite => self.1.spec_with_eoc().lemma_parse_sound_value(bytes),
                }
                let value = match branch {
                    L(value) => value,
                    R(value) => value,
                };
                lemma_ber_sequence_consistent(self.0, self.1, value);
            }
        }
    }

    impl<C: BerSeqBody + GoodSerializer> GoodSerializer for BerSequenceFmt<C> where
        C::WithEoc: GoodSerializer,
     {
        open spec fn serialize_inv(&self) -> bool {
            self.1.serialize_inv() && self.1.spec_with_eoc().serialize_inv()
        }

        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            ber_sequence_fmt(self.0, self.1).lemma_serialize_len(value);
        }
    }

    impl<C: BerSeqBody + GoodSerializer + EquivSerializers> NonTailFmt for BerSequenceFmt<C> where
        C::WithEoc: NonTailFmt,
     {
        open spec fn serialize_dps_inv(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_inv()
            &&& self.1.spec_with_eoc().serialize_dps_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, obuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<C: BerSeqBody + EquivSerializers> EquivSerializersGeneral for BerSequenceFmt<C> where
        C::WithEoc: EquivSerializersGeneral,
     {
        open spec fn equiv_general_inv(&self) -> bool {
            self.1.equiv_inv() && self.1.spec_with_eoc().equiv_general_inv()
        }

        proof fn lemma_serialize_equiv(&self, value: Self::SVal, obuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).lemma_serialize_equiv(value, obuf);
        }
    }

    impl<C: BerSeqBody + EquivSerializers> EquivSerializers for BerSequenceFmt<C> where
        C::WithEoc: EquivSerializersGeneral,
     {
        open spec fn equiv_inv(&self) -> bool {
            self.equiv_general_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<C> SPRoundTripDps for BerSequenceFmt<C> where
        C: BerSeqBody + GoodSerializer + EquivSerializers + SPRoundTripDps,
        C::WithEoc: SPRoundTripDps,
     {
        open spec fn unambiguous(&self) -> bool {
            &&& self.1.serialize_inv()
            &&& self.1.equiv_inv()
            &&& self.1.unambiguous()
            &&& self.1.spec_with_eoc().unambiguous()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, obuf: Seq<u8>) {
            ber_sequence_fmt(self.0, self.1).theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

impl<'i, C> Parser<&'i [u8]> for BerSequenceFmt<C> where
    C: BerSeqBody + Parser<&'i [u8]> + SafeParser,
    C::WithEoc: Parser<&'i [u8], PT = C::PT> + SafeParser,
 {
    type PT = C::PT;

    fn min_byte_len(&self) -> usize {
        // An empty value has an identifier and a length octet.
        2
    }

    open spec fn exec_inv(&self) -> bool {
        &&& self.1.exec_inv()
        &&& self.1.safe_inv()
        &&& self.1.spec_with_eoc().exec_inv()
        &&& self.1.spec_with_eoc().safe_inv()
    }

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;

        let _ = ibuf.len();
        let (tag_len, _tag) = Const(TagFmt, self.0).parse(ibuf)?;
        let after_tag = ibuf.skip(tag_len);
        let (length_len, length) = BerLengthFmt.parse(&after_tag)?;
        let content = after_tag.skip(length_len);

        let (content_len, value) = match length {
            BerLength::Definite(len) => ExactLen(len, self.1).parse(&content)?,
            BerLength::Indefinite => {
                let framed = self.1.with_eoc();
                framed.parse(&content)?
            },
        };
        let total = tag_len + length_len + content_len;
        assert(self.spec_parse(ibuf@) == Some((total as int, value.deep_view())));
        Ok((total, value))
    }
}

impl<Output: OutputBuf, C, T> Serializer<Output, T> for BerSequenceFmt<C> where
    T: DeepView + ?Sized,
    C: BerSeqBody + Serializer<Output, T> + ByteLen<T>,
 {
    #[verifier::prophetic]
    open spec fn exec_inv(&self) -> bool {
        &&& <C as Serializer<Output, T>>::exec_inv(&self.1)
        &&& <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn serialize_into(&self, value: &T, obuf: &mut Output) {
        proof {
            obuf.lemma_fits_len_bound(self.byte_len(value.deep_view()));
            lemma_content_len(self.0, self.1, value.deep_view());
            lemma_definite(self.0, self.1, value.deep_view());
        }
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        normalized.serialize_into(value, obuf);
    }
}

impl<C, T> Prepare<T> for BerSequenceFmt<C> where T: DeepView + ?Sized, C: BerSeqBody + Prepare<T> {
    open spec fn exec_inv(&self) -> bool {
        <C as Prepare<T>>::exec_inv(&self.1)
    }

    fn prepare(&self, value: &T) -> Result<usize, PreSerializeError> {
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        let result = normalized.prepare(value);
        proof {
            if result is Ok {
                crate::asn1::tlv::lemma_asn1_consistent::<_, BER>(
                    self.0,
                    self.1,
                    value.deep_view(),
                );
                lemma_definite(self.0, self.1, value.deep_view());
            }
        }
        result
    }
}

impl<C, T> ByteLen<T> for BerSequenceFmt<C> where T: DeepView + ?Sized, C: BerSeqBody + ByteLen<T> {
    open spec fn exec_inv(&self) -> bool {
        <C as ByteLen<T>>::exec_inv(&self.1)
    }

    fn length(&self, value: &T) -> usize {
        proof {
            lemma_content_len(self.0, self.1, value.deep_view());
            lemma_definite(self.0, self.1, value.deep_view());
        }
        let normalized = ASN1Fmt::<_, BER>(self.0, self.1);
        normalized.length(value)
    }
}

} // verus!
#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;
    use crate::asn1::ber::{BOOLEAN, DEFAULT, EXPLICIT, INTEGER8, SEQUENCE};
    use crate::core::exec::SerializerExt;

    #[test]
    fn optional_body_consumes_eoc_and_leaves_the_continuation() {
        let fmt = SEQUENCE(Optional(BOOLEAN, Eof));
        let empty = [0x30, 0x80, 0, 0, 0xaa];
        assert_eq!(fmt.parse(&&empty[..]).unwrap(), (4, (None, ())));
        let present = [0x30, 0x80, 1, 1, 1, 0, 0, 0xaa];
        let (n, value) = fmt.parse(&&present[..]).unwrap();
        assert_eq!(n, 7);
        assert_eq!(value, (Some(true), ()));
        let mut output = alloc::vec![0; fmt.prepare(&value).unwrap()];
        fmt.serialize(&value, &mut output);
        assert_eq!(output, [0x30, 3, 1, 1, 0xff]);
    }

    #[test]
    fn default_body_accepts_present_and_absent_default() {
        let fmt = SEQUENCE(DEFAULT(BOOLEAN, false, Eof));
        for bytes in [&[0x30, 0x80, 0, 0][..], &[0x30, 0x80, 1, 1, 0, 0, 0][..]] {
            let (n, value) = fmt.parse(&bytes).unwrap();
            assert_eq!(n, bytes.len());
            assert_eq!(value, (false, ()));
            let mut output = alloc::vec![0; fmt.prepare(&value).unwrap()];
            fmt.serialize(&value, &mut output);
            assert_eq!(output, [0x30, 0]);
        }
    }

    #[test]
    fn explicit_terminal_belongs_to_the_wrapper() {
        let fmt = EXPLICIT(0, INTEGER8);
        let input = [0xa0, 0x80, 2, 1, 7, 0, 0, 0xaa];
        let (n, value) = fmt.parse(&&input[..]).unwrap();
        assert_eq!((n, value), (7, 7i8));
        let mut output = alloc::vec![0; fmt.prepare(&value).unwrap()];
        fmt.serialize(&value, &mut output);
        assert_eq!(output, [0xa0, 3, 2, 1, 7]);
    }
}
