//! BER ANY open type and capture wrappers.
#[cfg(feature = "alloc")]
use crate::asn1::AnyOwned;
use crate::asn1::{AnyFmt, AnySpec, BerLength, BerLengthFmt, Tag, TagFmt, BER};
use crate::combinators::{
    bytes::ExactLen,
    mapped::spec::FnSpecMapper,
    recursive::{
        BundledSpecs, EquivSerializersGeneralRecBody, GoodSerializerRecBody, ParamRecSpecs,
        ParserRecBody, ProductiveRecBody, SafeParserRecBody, SpecRecBody,
    },
    Bind, Const, FixWith, Mapped, Pair, Repeat, Sum, Tail, Void, U8,
};
use crate::core::exec::fns::*;
use crate::core::exec::parser::*;
use crate::core::exec::{
    input::InputBuf, ByteLen, OutputBuf, PResult, ParseError, PreSerializeError, Prepare,
    Serializer,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;
#[cfg(feature = "alloc")]
use vstd::slice::slice_to_vec;

use Sum::Inl as L;
use Sum::Inr as R;

verus! {

/// Exact BER end-of-contents marker: the universal primitive EOC tag followed by a zero length
/// octet (`00 00`).
pub type EocFmt = Pair<Const<TagFmt, Tag>, Const<U8, u8>>;

/// Parsed value of [`EocFmt`]. BER framing discards this value after recognizing the marker.
pub(super) type EocValue = (Tag, u8);

/// Exact BER end-of-contents marker (`00 00`).
pub const EOC: EocFmt = Pair(Const(TagFmt, TagFmt::EOC), Const(U8, 0u8));

pub(super) open spec fn discard_eoc_result<T>(result: Option<(int, (T, EocValue))>) -> Option<
    (int, T),
> {
    match result {
        Some((n, (value, _eoc))) => Some((n, value)),
        None => None,
    }
}

pub(super) fn parse_discard_eoc<I, P, T>(parser: &P, input: &I) -> (result: PResult<T>) where
    I: InputBuf,
    T: DeepView,
    P: Parser<I, PT = (T, EocValue), PVal = (T::V, EocValue)>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(result, discard_eoc_result(parser.spec_parse(input@))),
{
    let (n, (value, _eoc)) = parser.parse(input)?;
    Ok((n, value))
}

/// Zero-width boundary marker for the contents of a schema-defined BER constructed value.
///
/// It succeeds at the end of a definite-length input or immediately before EOC. In the latter
/// case it deliberately leaves EOC unconsumed for the enclosing indefinite-length framing
/// combinator. Serialization emits no bytes.
#[derive(Clone, Copy)]
pub struct BerEndFmt;

/// BER constructed-content boundary.
pub const BER_END: BerEndFmt = BerEndFmt;

pub open spec fn at_ber_end(input: Seq<u8>) -> bool {
    input.len() == 0 || EOC.spec_parse(input) is Some
}

impl SpecParser for BerEndFmt {
    type PVal = ();

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        if at_ber_end(input) {
            Some((0, ()))
        } else {
            None
        }
    }
}

impl Consistency for BerEndFmt {
    type Val = ();

    open spec fn consistent(&self, _value: Self::Val) -> bool {
        true
    }
}

impl AdmitsUniqueVal for BerEndFmt {
    proof fn lemma_unique_consistent_val(&self, _left: Self::Val, _right: Self::Val) {
    }
}

impl SpecSerializerDps for BerEndFmt {
    type SValue = ();

    open spec fn spec_serialize_dps(&self, _value: Self::SValue, _obuf: Seq<u8>) -> Seq<u8> {
        Seq::empty()
    }
}

impl SpecSerializer for BerEndFmt {
    type SVal = ();

    open spec fn spec_serialize(&self, _value: Self::SVal) -> Seq<u8> {
        Seq::empty()
    }
}

impl SpecByteLen for BerEndFmt {
    type T = ();

    open spec fn byte_len(&self, _value: Self::T) -> nat {
        0
    }
}

impl SafeParser for BerEndFmt {
    proof fn lemma_parse_safe(&self, _input: Seq<u8>) {
    }
}

impl Productive for BerEndFmt {
    open spec fn productive_inv(&self) -> bool {
        false
    }

    proof fn lemma_productive(&self, _input: Seq<u8>) {
    }
}

impl GoodSerializer for BerEndFmt {
    proof fn lemma_serialize_len(&self, _value: Self::SVal) {
    }
}

impl EquivSerializers for BerEndFmt {
    proof fn lemma_serialize_equiv_on_empty(&self, _value: Self::SVal) {
    }
}

impl SPRoundTripDps for BerEndFmt {
    proof fn theorem_serialize_dps_parse_roundtrip(&self, _value: Self::T, _obuf: Seq<u8>) {
    }
}

impl<'i> Parser<&'i [u8]> for BerEndFmt {
    type PT = ();

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;

        proof {
            crate::core::exec::bridge_lemmas::lemma_pair_parser_exec_inv::<&'i [u8], _, _>(&EOC);
        }
        if input.len() == 0 {
            Ok((0, ()))
        } else {
            match EOC.parse(input) {
                Ok(_) => Ok((0, ())),
                Err(_) => Err(ParseError::custom("expected end of BER constructed contents")),
            }
        }
    }
}

impl<Output: OutputBuf> Serializer<Output, ()> for BerEndFmt {
    fn serialize_into(&self, _value: &(), _obuf: &mut Output) {
        broadcast use crate::core::exec::output::outbuf_lemmas;

    }
}

impl Prepare<()> for BerEndFmt {
    fn prepare(&self, _value: &()) -> Result<usize, PreSerializeError> {
        Ok(0)
    }
}

impl ByteLen<()> for BerEndFmt {
    fn length(&self, _value: &()) -> usize {
        0
    }
}

/// A parsed value together with the exact octets consumed for it.
///
/// Recursive BER ANY needs this small internal layer because the contents of an
/// indefinite-length parent are the original child TLVs, including any legal
/// non-canonical BER tag or length encodings.
#[verifier::ext_equal]
#[doc(hidden)]
pub struct Captured<T> {
    pub value: T,
    pub encoded: Seq<u8>,
}

/// Specification-only wrapper retaining the exact input prefix consumed by `C`.
#[doc(hidden)]
pub struct Capture<C>(pub C);

impl<C: SpecParser> SpecParser for Capture<C> {
    type PVal = Captured<C::PVal>;

    open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
        match self.0.spec_parse(input) {
            Some((n, value)) => Some((n, Captured { value, encoded: input.take(n) })),
            None => None,
        }
    }
}

impl<C: SpecCombinator> Consistency for Capture<C> {
    type Val = Captured<C::T>;

    open spec fn consistent(&self, value: Self::Val) -> bool {
        self.0.consistent(value.value)
    }
}

impl<C: SpecCombinator> SpecSerializerDps for Capture<C> {
    type SValue = Captured<C::T>;

    open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
        value.encoded + obuf
    }
}

impl<C: SpecCombinator> SpecSerializer for Capture<C> {
    type SVal = Captured<C::T>;

    open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
        value.encoded
    }
}

impl<C: SpecCombinator> SpecByteLen for Capture<C> {
    type T = Captured<C::T>;

    open spec fn byte_len(&self, value: Self::T) -> nat {
        value.encoded.len()
    }
}

impl<C: SpecCombinator + SafeParser> SafeParser for Capture<C> {
    open spec fn safe_inv(&self) -> bool {
        self.0.safe_inv()
    }

    proof fn lemma_parse_safe(&self, input: Seq<u8>) {
        self.0.lemma_parse_safe(input);
    }
}

impl<C: SpecCombinator + Productive> Productive for Capture<C> {
    open spec fn productive_inv(&self) -> bool {
        self.0.productive_inv()
    }

    proof fn lemma_productive(&self, input: Seq<u8>) {
        self.0.lemma_productive(input);
    }
}

type BerAnyWireType = (
    Tag,
    Sum<(BerLength, Sum<Seq<u8>, Sum<(Seq<Captured<AnySpec>>, EocValue), Never>>), Never>,
);

type BerAnyRawBodyFmt<Rec> = Bind<
    TagFmt,
    spec_fn(Tag) -> Sum<
        Bind<
            BerLengthFmt,
            spec_fn(BerLength) -> Sum<ExactLen<Tail, usize>, Sum<Repeat<Rec, EocFmt>, Void>>,
        >,
        Void,
    >,
>;

type BerAnyMappedBodyFmt<Rec> = Mapped<
    BerAnyRawBodyFmt<Rec>,
    FnSpecMapper<BerAnyWireType, AnySpec>,
>;

type BerAnyBodyFmt<Rec> = Capture<BerAnyMappedBodyFmt<Rec>>;

pub open spec fn captured_any_contents(children: Seq<Captured<AnySpec>>) -> Seq<u8> {
    children.map(|_i: int, child: Captured<AnySpec>| child.encoded).flatten()
}

/// One recursive unfolding of a BER open type.
///
/// Definite values retain their opaque contents. Indefinite values are legal only for
/// constructed tags and retain the exact encodings of their child TLVs, excluding the
/// terminating EOC. EOC itself is never accepted as an ANY value.
pub open spec fn ber_any_rec_body(rec: ParamRecSpecs<(), Captured<AnySpec>>) -> BerAnyBodyFmt<
    BundledSpecs<Captured<AnySpec>>,
> {
    #[verusfmt::skip]
    Capture(Mapped {
        inner: Bind(TagFmt, |tag: Tag|
            if tag == TagFmt::EOC {
                R(Void("EOC is not an open-type value"))
            } else {
                L(Bind(BerLengthFmt, |length: BerLength|
                    match length {
                        BerLength::Definite(len) =>
                            L(ExactLen(len, Tail)),
                        BerLength::Indefinite if tag.constructed =>
                            R(L(Repeat(rec(()), EOC))),
                        BerLength::Indefinite =>
                            R(R(Void("Primitive values cannot use indefinite length"))),
                    },
                ))
            },
        ),
        mapper: (
            |parsed: BerAnyWireType| {
                match parsed.1 {
                    L((_length, L(content))) =>
                        AnySpec { tag: parsed.0, content },
                    L((_length, R(L((children, _eoc))))) =>
                        AnySpec {
                            tag: parsed.0,
                            content: captured_any_contents(children),
                        },
                    L((_length, R(R(_)))) => arbitrary(),
                    R(_) => arbitrary(),
                }
            },
            |value: AnySpec| (
                value.tag,
                L((
                    BerLength::Definite(value.content.len() as usize),
                    L(value.content),
                )),
            ),
        ),
    })
}

pub struct BerAnyRecBody;

impl SpecRecBody for BerAnyRecBody {
    type Param = ();

    type T = Captured<AnySpec>;

    type Body = BerAnyBodyFmt<BundledSpecs<Captured<AnySpec>>>;

    open spec fn spec_body(
        &self,
        _param: (),
        rec: ParamRecSpecs<(), Captured<AnySpec>>,
    ) -> Self::Body {
        ber_any_rec_body(rec)
    }
}

mod recursive_proofs {
    use super::*;

    impl SafeParserRecBody for BerAnyRecBody {
        proof fn lemma_body_safe_inv_preservation(
            &self,
            _param: (),
            rec: ParamRecSpecs<(), Captured<AnySpec>>,
        ) {
        }
    }

    impl ProductiveRecBody for BerAnyRecBody {
        proof fn lemma_body_productive_inv_preservation(
            &self,
            _param: (),
            rec: ParamRecSpecs<(), Captured<AnySpec>>,
        ) {
        }
    }

}

/// BER ANY/open type with bounded nesting for indefinite-length constructed values.
///
/// Parsing accepts definite values and recursively framed indefinite constructed values.
/// Serialization is normalized to a definite-length encoding.
#[derive(Clone, Copy)]
pub struct BerAnyFmt<const LIMIT: usize>;

pub open spec fn ber_any_parse<const LIMIT: usize>(input: Seq<u8>) -> Option<(int, AnySpec)> {
    match AnyFmt::<BER>.spec_parse(input) {
        Some(parsed) => Some(parsed),
        None => match FixWith::<LIMIT, _, _>(BerAnyRecBody, ()).spec_parse(input) {
            Some((n, captured)) => Some((n, captured.value)),
            None => None,
        },
    }
}

mod derived_specs {
    use super::*;

    impl<const LIMIT: usize> SpecParser for BerAnyFmt<LIMIT> {
        type PVal = AnySpec;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            ber_any_parse::<LIMIT>(input)
        }
    }

    impl<const LIMIT: usize> Consistency for BerAnyFmt<LIMIT> {
        type Val = AnySpec;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            AnyFmt::<BER>.consistent(value)
        }
    }

    impl<const LIMIT: usize> SpecSerializerDps for BerAnyFmt<LIMIT> {
        type SValue = AnySpec;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, obuf: Seq<u8>) -> Seq<u8> {
            AnyFmt::<BER>.spec_serialize_dps(value, obuf)
        }
    }

    impl<const LIMIT: usize> SpecSerializer for BerAnyFmt<LIMIT> {
        type SVal = AnySpec;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            AnyFmt::<BER>.spec_serialize(value)
        }
    }

    impl<const LIMIT: usize> SpecByteLen for BerAnyFmt<LIMIT> {
        type T = AnySpec;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            AnyFmt::<BER>.byte_len(value)
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const LIMIT: usize> SafeParser for BerAnyFmt<LIMIT> {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            AnyFmt::<BER>.lemma_parse_safe(input);
            FixWith::<LIMIT, _, _>(BerAnyRecBody, ()).lemma_parse_safe(input);
        }
    }

    impl<const LIMIT: usize> Productive for BerAnyFmt<LIMIT> {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            AnyFmt::<BER>.lemma_productive(input);
            FixWith::<LIMIT, _, _>(BerAnyRecBody, ()).lemma_productive(input);
        }
    }

    impl<const LIMIT: usize> GoodSerializer for BerAnyFmt<LIMIT> {
        proof fn lemma_serialize_len(&self, value: AnySpec) {
            AnyFmt::<BER>.lemma_serialize_len(value);
        }
    }

    impl<const LIMIT: usize> NonTailFmt for BerAnyFmt<LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: AnySpec, obuf: Seq<u8>) {
            AnyFmt::<BER>.lemma_serialize_dps_prepend(value, obuf);
        }

        proof fn lemma_serialize_dps_len(&self, value: AnySpec, obuf: Seq<u8>) {
            AnyFmt::<BER>.lemma_serialize_dps_len(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializersGeneral for BerAnyFmt<LIMIT> {
        proof fn lemma_serialize_equiv(&self, value: AnySpec, obuf: Seq<u8>) {
            AnyFmt::<BER>.lemma_serialize_equiv(value, obuf);
        }
    }

    impl<const LIMIT: usize> EquivSerializers for BerAnyFmt<LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: AnySpec) {
            self.lemma_serialize_equiv(value, Seq::empty());
        }
    }

    impl<const LIMIT: usize> SPRoundTripDps for BerAnyFmt<LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: AnySpec, obuf: Seq<u8>) {
            AnyFmt::<BER>.theorem_serialize_dps_parse_roundtrip(value, obuf);
        }
    }

}

#[cfg(feature = "alloc")]
impl<Output: OutputBuf, const LIMIT: usize> Serializer<Output, AnyOwned> for BerAnyFmt<LIMIT> {
    fn serialize_into(&self, value: &AnyOwned, obuf: &mut Output) {
        AnyFmt::<BER>.serialize_into(value, obuf)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> Prepare<AnyOwned> for BerAnyFmt<LIMIT> {
    fn prepare(&self, value: &AnyOwned) -> Result<usize, PreSerializeError> {
        AnyFmt::<BER>.prepare(value)
    }
}

#[cfg(feature = "alloc")]
impl<const LIMIT: usize> ByteLen<AnyOwned> for BerAnyFmt<LIMIT> {
    fn length(&self, value: &AnyOwned) -> usize {
        AnyFmt::<BER>.length(value)
    }
}

#[cfg(feature = "alloc")]
#[doc(hidden)]
pub struct CapturedAnyOwned {
    pub value: AnyOwned,
    pub encoded: Vec<u8>,
}

#[cfg(feature = "alloc")]
impl DeepView for CapturedAnyOwned {
    type V = Captured<AnySpec>;

    closed spec fn deep_view(&self) -> Self::V {
        Captured { value: self.value.deep_view(), encoded: self.encoded.deep_view() }
    }
}

#[cfg(feature = "alloc")]
fn flatten_captured_any_contents(children: Vec<CapturedAnyOwned>) -> (content: Vec<u8>)
    ensures
        content.deep_view() == captured_any_contents(children.deep_view()),
{
    broadcast use vstd::seq_lib::group_seq_properties;

    let ghost child_views = children.deep_view();
    let ghost encoded_views = child_views.map(|_i: int, child: Captured<AnySpec>| child.encoded);
    let mut content = Vec::new();
    for i in 0..children.len()
        invariant
            children.deep_view() == child_views,
            encoded_views == child_views.map(|_i: int, child: Captured<AnySpec>| child.encoded),
            content.deep_view() == encoded_views.take(i as int).flatten(),
    {
        let encoded = children[i].encoded.as_slice();
        proof {
            let prefix = encoded_views.take(i as int);
            prefix.lemma_flatten_push(encoded.deep_view());
            assert(encoded_views[i as int] == encoded.deep_view());
            assert(encoded_views.take(i as int + 1) == prefix.push(encoded.deep_view()));
        }
        content.extend_from_slice(encoded);
    }
    content
}

#[cfg(feature = "alloc")]
spec fn flattened_captured_any_result(
    result: Option<(int, (Seq<Captured<AnySpec>>, EocValue))>,
) -> Option<(int, Seq<u8>)> {
    match result {
        Some((n, (children, _eoc))) => Some((n, captured_any_contents(children))),
        None => None,
    }
}

#[cfg(feature = "alloc")]
fn parse_captured_any_children<I, P>(parser: &P, input: &I) -> (result: PResult<Vec<u8>>) where
    I: InputBuf,
    P: Parser<I, PT = (Vec<CapturedAnyOwned>, EocValue), PVal = (Seq<Captured<AnySpec>>, EocValue)>,

    requires
        parser.exec_inv(),
    ensures
        parse_matches_spec(result, flattened_captured_any_result(parser.spec_parse(input@))),
{
    let (n, (children, _eoc)) = parser.parse(input)?;
    let content = flatten_captured_any_contents(children);
    Ok((n, content))
}

#[cfg(feature = "alloc")]
impl<'i> ParserRecBody<&'i [u8]> for BerAnyRecBody {
    type EP = ();

    type O = CapturedAnyOwned;

    fn parse_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<(), Captured<AnySpec>>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<CapturedAnyOwned> where Exec: Fn(&(), &&'i [u8]) -> PResult<CapturedAnyOwned> {
        use crate::combinators::congruence::*;
        use crate::core::exec::bridge_lemmas::*;

        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use crate::asn1::tag::lemma_const_tag_fmt_exec_inv;
        broadcast use lemma_parser_congruent_reflexive;

        let _ = ibuf.len();
        let (tag_len, tag) = TagFmt.parse(ibuf)?;
        if tag == TagFmt::EOC {
            return Err(ParseError::invalid_tag());
        }
        let after_tag = ibuf.skip(tag_len);
        let (length_len, length) = BerLengthFmt.parse(&after_tag)?;
        let contents = after_tag.skip(length_len);

        let (content_len, value) = match length {
            BerLength::Definite(len) => {
                let (content_len, content) = ExactLen(len, Tail).parse(&contents)?;
                let content = slice_to_vec(content);
                let value = AnyOwned::new(tag, content);
                (content_len, value)
            },
            BerLength::Indefinite => {
                if !tag.constructed {
                    return Err(ParseError::custom("Primitive values cannot use indefinite length"));
                }
                let ghost child_spec = spec_rec(());
                let child_exec = |input: &&'i [u8]| -> (r: PResult<CapturedAnyOwned>)
                    ensures
                        parse_matches_spec(r, child_spec.2(input@)),
                    { exec_rec(&(), input) };
                let child: &FnParser<
                    &'i [u8],
                    CapturedAnyOwned,
                    BundledSpecs<Captured<AnySpec>>,
                    _,
                > = &FnParser::new(child_exec, Ghost(child_spec));
                proof {
                    lemma_ref_parser_exec_inv::<&'i [u8], _>(child);
                    lemma_ref_safe_productive_inv(child);
                    lemma_ref_fn_parser_congruence(child);
                }
                let repeated = Repeat(child, EOC);
                proof {
                    lemma_pair_parser_exec_inv::<&'i [u8], _, _>(&EOC);
                    lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                    lemma_repeat_parser_congruence(child, child_spec, EOC, EOC);
                    reveal(parser_congruent);
                }
                let (content_len, content) = parse_captured_any_children(&repeated, &contents)?;
                let value = AnyOwned::new(tag, content);
                (content_len, value)
            },
        };

        let total = tag_len + length_len + content_len;
        let encoded = slice_to_vec(ibuf.take(total));
        Ok((total, CapturedAnyOwned { value, encoded }))
    }
}

#[cfg(feature = "alloc")]
impl<'i, const LIMIT: usize> Parser<&'i [u8]> for BerAnyFmt<LIMIT> {
    type PT = AnyOwned;

    fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
        match AnyFmt::<BER>.parse(ibuf) {
            Ok((n, value)) => {
                let tag = value.tag();
                let content = slice_to_vec(value.content());
                Ok((n, AnyOwned::new(tag, content)))
            },
            Err(_) => {
                let (n, captured) = FixWith::<LIMIT, _, _>(BerAnyRecBody, ()).parse(ibuf)?;
                Ok((n, captured.value))
            },
        }
    }
}

} // verus!
