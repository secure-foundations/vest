//! Recursive generic-CBOR format specifications and implementations.
use alloc::{boxed::Box, string::String, vec::Vec};

use crate::asn1::Utf8StringFmt;
use crate::combinators::{
    bytes::ExactLen,
    mapped::spec::{FnSpecMapper, LosslessMapper, LossyMapper, SpecMapper},
    recursive::{
        BundledSpecs, EquivSerializersGeneralRecBody, GoodSerializerRecBody, NonMalleableRecBody,
        NonTailFmtRecBody, ParamRecSpecs, ParserRecBody, PrepareRecBody, ProductiveRecBody,
        SPRoundTripDpsRecBody, SafeParserRecBody, SerializerRecBody, SoundParserRecBody,
        SpecRecBody,
    },
    Bind, Empty, FixWith, Mapped, Pair, Repeat, RepeatN, Sum, Tail, Void,
};
use crate::core::exec::{
    fns::{FnByteLen, FnParser, FnPrepare, FnSerializer},
    input::{InputBuf, InputSlice},
    output::OutputBuf,
    parser::*,
    serializer::{ByteLen, PreSerializeError, Prepare, Serializer},
    ParseError,
};
use crate::core::{proof::*, spec::*};
use crate::Never;
use vstd::assert_seqs_equal;
use vstd::prelude::*;
use vstd::string::StringSliceAdditionalSpecFns;

use super::{
    CborBytes, CborFloat, CborHead, CborHeadFmt, CborHeadValue, CborText, CborValue, CborValueSpec,
    MajorType, BREAK, MAX_RECURSION_DEPTH,
};
use Sum::Inl as L;
use Sum::Inr as R;

use super::chunk::{flatten_byte_chunks, flatten_text_chunks, ByteChunkFmt, TextChunkFmt};

verus! {

type CborWire = (
    CborHead,
    Sum<
        (),
        Sum<
            (),
            Sum<
                Seq<u8>,
                Sum<
                    (Seq<Seq<u8>>, u8),
                    Sum<
                        Seq<char>,
                        Sum<
                            (Seq<Seq<char>>, u8),
                            Sum<
                                Seq<CborValueSpec>,
                                Sum<
                                    (Seq<CborValueSpec>, u8),
                                    Sum<
                                        Seq<(CborValueSpec, CborValueSpec)>,
                                        Sum<
                                            (Seq<(CborValueSpec, CborValueSpec)>, u8),
                                            Sum<CborValueSpec, Sum<(), Never>>,
                                        >,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
);

type CborBranches<Rec, const DET: bool> = Sum<
    Empty,
    Sum<
        Empty,
        Sum<
            ExactLen<Tail, u64>,
            Sum<
                Repeat<ByteChunkFmt<DET>, super::BreakFmt>,
                Sum<
                    ExactLen<Utf8StringFmt, u64>,
                    Sum<
                        Repeat<TextChunkFmt<DET>, super::BreakFmt>,
                        Sum<
                            RepeatN<Rec, u64>,
                            Sum<
                                Repeat<Rec, super::BreakFmt>,
                                Sum<
                                    RepeatN<Pair<Rec, Rec>, u64>,
                                    Sum<
                                        Repeat<Pair<Rec, Rec>, super::BreakFmt>,
                                        Sum<Rec, Sum<Empty, Void>>,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
>;

type CborParseBodyInnerFmt<Rec, const DET: bool> = Mapped<
    Bind<CborHeadFmt<DET>, spec_fn(CborHead) -> CborBranches<Rec, DET>>,
    CborMapper<DET>,
>;

type NormalizedOnly<T> = Mapped<Void, FnSpecMapper<Never, T>>;

pub open spec fn normalized_only<T>() -> NormalizedOnly<T> {
    Mapped {
        inner: Void("indefinite-length form is not emitted"),
        mapper: (|_never: Never| arbitrary(), |_value: T| arbitrary()),
    }
}

type CborNormalizedBranches<Rec, const DET: bool> = Sum<
    Empty,
    Sum<
        Empty,
        Sum<
            ExactLen<Tail, u64>,
            Sum<
                NormalizedOnly<(Seq<Seq<u8>>, u8)>,
                Sum<
                    ExactLen<Utf8StringFmt, u64>,
                    Sum<
                        NormalizedOnly<(Seq<Seq<char>>, u8)>,
                        Sum<
                            RepeatN<Rec, u64>,
                            Sum<
                                NormalizedOnly<(Seq<CborValueSpec>, u8)>,
                                Sum<
                                    RepeatN<Pair<Rec, Rec>, u64>,
                                    Sum<
                                        NormalizedOnly<(Seq<(CborValueSpec, CborValueSpec)>, u8)>,
                                        Sum<Rec, Sum<Empty, Void>>,
                                    >,
                                >,
                            >,
                        >,
                    >,
                >,
            >,
        >,
    >,
>;

type CborNormalizedBodyInnerFmt<Rec, const DET: bool> = Mapped<
    Bind<CborHeadFmt<DET>, spec_fn(CborHead) -> CborNormalizedBranches<Rec, DET>>,
    CborMapper<DET>,
>;

pub open spec fn cbor_value_valid(value: CborValueSpec) -> bool {
    match value {
        CborValueSpec::Integer(value) => {
            &&& value as int >= -1 - u64::MAX as int
            &&& value as int <= u64::MAX as int
        },
        CborValueSpec::Bytes(bytes) => bytes.len() <= u64::MAX,
        CborValueSpec::Text(text) => vstd::utf8::encode_utf8(text).len() <= u64::MAX,
        CborValueSpec::Array(values) => values.len() <= u64::MAX,
        CborValueSpec::Map(entries) => entries.len() <= u64::MAX,
        CborValueSpec::Simple(value) => value <= 19u8 || value >= 32u8,
        _ => true,
    }
}

pub open spec fn cbor_wire_valid<const DET: bool>(wire: CborWire) -> bool {
    #[verusfmt::skip]
    match wire {
        (CborHead { major: MajorType::Unsigned, value: CborHeadValue::Argument(_) }, L(())) => true,
        (CborHead { major: MajorType::Negative, value: CborHeadValue::Argument(_) }, R(L(()))) => true,
        (CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) }, R(R(L(bytes)))) => len == bytes.len(),
        (CborHead { major: MajorType::Bytes, value: CborHeadValue::Indefinite }, R(R(R(L(_))))) => !DET,
        (CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) }, R(R(R(R(L(text)))))) => len == vstd::utf8::encode_utf8(text).len(),
        (CborHead { major: MajorType::Text, value: CborHeadValue::Indefinite }, R(R(R(R(R(L(_))))))) => !DET,
        (CborHead { major: MajorType::Array, value: CborHeadValue::Argument(len) }, R(R(R(R(R(R(L(values)))))))) => len == values.len(),
        (CborHead { major: MajorType::Array, value: CborHeadValue::Indefinite }, R(R(R(R(R(R(R(L(_))))))))) => !DET,
        (CborHead { major: MajorType::Map, value: CborHeadValue::Argument(len) }, R(R(R(R(R(R(R(R(L(entries)))))))))) => len == entries.len(),
        (CborHead { major: MajorType::Map, value: CborHeadValue::Indefinite }, R(R(R(R(R(R(R(R(R(L(_))))))))))) => !DET,
        (CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(_) }, R(R(R(R(R(R(R(R(R(R(L(_)))))))))))) => true,
        (CborHead { major: MajorType::Simple, value }, R(R(R(R(R(R(R(R(R(R(R(L(()))))))))))))) => match value {
            CborHeadValue::Float(_) => true,
            CborHeadValue::Simple(value) => value <= 23u8 || value >= 32u8,
            _ => false,
        },
        _ => false,
    }
}

pub open spec fn decode_cbor_wire(wire: CborWire) -> CborValueSpec {
    let head = wire.0;
    #[verusfmt::skip]
    match wire.1 {
        L(()) => match head.value {
            CborHeadValue::Argument(value) => CborValueSpec::Integer(value as i128),
            _ => arbitrary(),
        },
        R(L(())) => match head.value {
            CborHeadValue::Argument(value) => CborValueSpec::Integer((-1 - value as int) as i128),
            _ => arbitrary(),
        },
        R(R(L(bytes))) => CborValueSpec::Bytes(bytes),
        R(R(R(L((chunks, _break))))) => CborValueSpec::Bytes(chunks.flatten()),
        R(R(R(R(L(text))))) => CborValueSpec::Text(text),
        R(R(R(R(R(L((chunks, _break))))))) => CborValueSpec::Text(chunks.flatten()),
        R(R(R(R(R(R(L(values))))))) => CborValueSpec::Array(values),
        R(R(R(R(R(R(R(L((values, _break))))))))) => CborValueSpec::Array(values),
        R(R(R(R(R(R(R(R(L(entries))))))))) => CborValueSpec::Map(entries),
        R(R(R(R(R(R(R(R(R(L((entries, _break))))))))))) => CborValueSpec::Map(entries),
        R(R(R(R(R(R(R(R(R(R(L(value))))))))))) => match head.value {
            CborHeadValue::Argument(tag) => CborValueSpec::Tag(tag, Box::new(value)),
            _ => arbitrary(),
        },
        R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))) => match head.value {
            CborHeadValue::Float(value) => CborValueSpec::Float(value),
            CborHeadValue::Simple(20) => CborValueSpec::Bool(false),
            CborHeadValue::Simple(21) => CborValueSpec::Bool(true),
            CborHeadValue::Simple(22) => CborValueSpec::Null,
            CborHeadValue::Simple(23) => CborValueSpec::Undefined,
            CborHeadValue::Simple(value) => CborValueSpec::Simple(value),
            _ => arbitrary(),
        },
        _ => arbitrary(),
    }
}

pub open spec fn encode_cbor_value(value: CborValueSpec) -> CborWire {
    #[verusfmt::skip]
    match value {
        CborValueSpec::Integer(value) if value >= 0 => (
            CborHead { major: MajorType::Unsigned, value: CborHeadValue::Argument(value as u64) },
            L(()),
        ),
        CborValueSpec::Integer(value) => (
            CborHead {
                major: MajorType::Negative,
                value: CborHeadValue::Argument((-1 - value as int) as u64),
            },
            R(L(())),
        ),
        CborValueSpec::Bytes(bytes) => (
            CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            },
            R(R(L(bytes))),
        ),
        CborValueSpec::Text(text) => (
            CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(vstd::utf8::encode_utf8(text).len() as u64),
            },
            R(R(R(R(L(text))))),
        ),
        CborValueSpec::Array(values) => (
            CborHead {
                major: MajorType::Array,
                value: CborHeadValue::Argument(values.len() as u64),
            },
            R(R(R(R(R(R(L(values))))))),
        ),
        CborValueSpec::Map(entries) => (
            CborHead {
                major: MajorType::Map,
                value: CborHeadValue::Argument(entries.len() as u64),
            },
            R(R(R(R(R(R(R(R(L(entries))))))))),
        ),
        CborValueSpec::Tag(tag, value) => (
            CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(tag) },
            R(R(R(R(R(R(R(R(R(R(L(*value))))))))))),
        ),
        CborValueSpec::Float(value) => (
            CborHead { major: MajorType::Simple, value: CborHeadValue::Float(value) },
            R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))),
        ),
        CborValueSpec::Bool(value) => (
            CborHead {
                major: MajorType::Simple,
                value: CborHeadValue::Simple(if value { 21 } else { 20 }),
            },
            R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))),
        ),
        CborValueSpec::Null => (
            CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(22) },
            R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))),
        ),
        CborValueSpec::Undefined => (
            CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(23) },
            R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))),
        ),
        CborValueSpec::Simple(value) => (
            CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(value) },
            R(R(R(R(R(R(R(R(R(R(R(L(())))))))))))),
        ),
    }
}

#[derive(Clone, Copy)]
pub struct CborMapper<const DET: bool>;

impl<const DET: bool> SpecMapper for CborMapper<DET> {
    type In = CborWire;

    type Out = CborValueSpec;

    open spec fn spec_map(&self, wire: Self::In) -> Self::Out {
        decode_cbor_wire(wire)
    }

    open spec fn spec_map_rev(&self, value: Self::Out) -> Self::In {
        encode_cbor_value(value)
    }

    open spec fn wf_in(&self, wire: Self::In) -> bool {
        cbor_wire_valid::<DET>(wire)
    }

    open spec fn wf_out(&self, value: Self::Out) -> bool {
        cbor_value_valid(value)
    }
}

impl<const DET: bool> LossyMapper for CborMapper<DET> {
    proof fn lemma_sound_mapper(&self, value: Self::Out) {
    }

    proof fn lemma_mapper_wf_out_in(&self, value: Self::Out) {
    }
}

impl LosslessMapper for CborMapper<true> {
    proof fn lemma_lossless_mapper(&self, wire: Self::In) {
        assert(cbor_wire_valid::<true>(wire));
        assert(encode_cbor_value(decode_cbor_wire(wire)) == wire);
    }

    proof fn lemma_mapper_wf_in_out(&self, wire: Self::In) {
    }
}

#[doc(hidden)]
pub open spec fn cbor_parse_body<const DET: bool>(
    rec: ParamRecSpecs<(), CborValueSpec>,
) -> CborParseBodyInnerFmt<BundledSpecs<CborValueSpec>, DET> {
    let child = rec(());
    #[verusfmt::skip]
    Mapped {
        inner: Bind(
            CborHeadFmt::<DET>,
            |head: CborHead|
                match head {
                    CborHead { major: MajorType::Unsigned, value: CborHeadValue::Argument(_) } => L(Empty),
                    CborHead { major: MajorType::Negative, value: CborHeadValue::Argument(_) } => R(L(Empty)),
                    CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) } => R(R(L(ExactLen(len, Tail)))),
                    CborHead { major: MajorType::Bytes, value: CborHeadValue::Indefinite } => R(R(R(L(Repeat(ByteChunkFmt::<DET>, BREAK))))),
                    CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) } => R(R(R(R(L(ExactLen(len, Utf8StringFmt)))))),
                    CborHead { major: MajorType::Text, value: CborHeadValue::Indefinite } => R(R(R(R(R(L(Repeat(TextChunkFmt::<DET>, BREAK))))))),
                    CborHead { major: MajorType::Array, value: CborHeadValue::Argument(len) } => R(R(R(R(R(R(L(RepeatN(len, child)))))))),
                    CborHead { major: MajorType::Array, value: CborHeadValue::Indefinite } => R(R(R(R(R(R(R(L(Repeat(child, BREAK))))))))),
                    CborHead { major: MajorType::Map, value: CborHeadValue::Argument(len) } => R(R(R(R(R(R(R(R(L(RepeatN(len, Pair(child, child))))))))))),
                    CborHead { major: MajorType::Map, value: CborHeadValue::Indefinite } => R(R(R(R(R(R(R(R(R(L(Repeat(Pair(child, child), BREAK))))))))))),
                    CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(_) } => R(R(R(R(R(R(R(R(R(R(L(child))))))))))),
                    CborHead { major: MajorType::Simple, value } if value != CborHeadValue::Break => R(R(R(R(R(R(R(R(R(R(R(L(Empty)))))))))))),
                    _ => R(R(R(R(R(R(R(R(R(R(R(R(Void("invalid CBOR head/value combination"))))))))))))),
                },
        ),
        mapper: CborMapper::<DET>,
    }
}

#[doc(hidden)]
pub open spec fn cbor_normalized_body<const DET: bool>(
    rec: ParamRecSpecs<(), CborValueSpec>,
) -> CborNormalizedBodyInnerFmt<BundledSpecs<CborValueSpec>, DET> {
    let child = rec(());
    #[verusfmt::skip]
    Mapped {
        inner: Bind(
            CborHeadFmt::<DET>,
            |head: CborHead|
                match head {
                    CborHead { major: MajorType::Unsigned, value: CborHeadValue::Argument(_) } => L(Empty),
                    CborHead { major: MajorType::Negative, value: CborHeadValue::Argument(_) } => R(L(Empty)),
                    CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) } => R(R(L(ExactLen(len, Tail)))),
                    CborHead { major: MajorType::Bytes, value: CborHeadValue::Indefinite } => R(R(R(L(normalized_only())))),
                    CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) } => R(R(R(R(L(ExactLen(len, Utf8StringFmt)))))),
                    CborHead { major: MajorType::Text, value: CborHeadValue::Indefinite } => R(R(R(R(R(L(normalized_only())))))),
                    CborHead { major: MajorType::Array, value: CborHeadValue::Argument(len) } => R(R(R(R(R(R(L(RepeatN(len, child)))))))),
                    CborHead { major: MajorType::Array, value: CborHeadValue::Indefinite } => R(R(R(R(R(R(R(L(normalized_only())))))))),
                    CborHead { major: MajorType::Map, value: CborHeadValue::Argument(len) } => R(R(R(R(R(R(R(R(L(RepeatN(len, Pair(child, child))))))))))),
                    CborHead { major: MajorType::Map, value: CborHeadValue::Indefinite } => R(R(R(R(R(R(R(R(R(L(normalized_only())))))))))),
                    CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(_) } => R(R(R(R(R(R(R(R(R(R(L(child))))))))))),
                    CborHead { major: MajorType::Simple, value } if value != CborHeadValue::Break => R(R(R(R(R(R(R(R(R(R(R(L(Empty)))))))))))),
                    _ => R(R(R(R(R(R(R(R(R(R(R(R(Void("invalid CBOR head/value combination"))))))))))))),
                },
        ),
        mapper: CborMapper::<DET>,
    }
}

proof fn lemma_normalized_parse_implies_parse<const DET: bool>(
    rec: ParamRecSpecs<(), CborValueSpec>,
    input: Seq<u8>,
)
    ensures
        cbor_normalized_body::<DET>(rec).spec_parse(input) matches Some((n, value))
            ==> cbor_parse_body::<DET>(rec).spec_parse(input) == Some((n, value)),
{
}

proof fn lemma_parse_normalized_consistency<const DET: bool>(
    rec: ParamRecSpecs<(), CborValueSpec>,
    value: CborValueSpec,
)
    ensures
        cbor_parse_body::<DET>(rec).consistent(value) == cbor_normalized_body::<DET>(
            rec,
        ).consistent(value),
{
}

proof fn lemma_parse_normalized_byte_len<const DET: bool>(
    rec: ParamRecSpecs<(), CborValueSpec>,
    value: CborValueSpec,
)
    ensures
        cbor_parse_body::<DET>(rec).byte_len(value) == cbor_normalized_body::<DET>(rec).byte_len(
            value,
        ),
{
}

/// One recursive CBOR unfolding with a permissive parser and normalized serializer semantics.
#[doc(hidden)]
pub struct CborBodyFmt<const DET: bool> {
    pub rec: Ghost<ParamRecSpecs<(), CborValueSpec>>,
}

pub open spec fn cbor_body<const DET: bool>(rec: ParamRecSpecs<(), CborValueSpec>) -> CborBodyFmt<
    DET,
> {
    CborBodyFmt { rec: Ghost(rec) }
}

pub struct CborRecBody<const DET: bool>;

impl<const DET: bool> SpecRecBody for CborRecBody<DET> {
    type Param = ();

    type T = CborValueSpec;

    type Body = CborBodyFmt<DET>;

    open spec fn spec_body(&self, _param: (), rec: ParamRecSpecs<(), CborValueSpec>) -> Self::Body {
        cbor_body::<DET>(rec)
    }
}

fn parse_cbor_with_child<'i, const DET: bool, P>(
    Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
    child: &P,
    input: &&'i [u8],
) -> (result: PResult<CborValue<'i>>) where
    P: Parser<&'i [u8], PT = CborValue<'i>, PVal = CborValueSpec> + Productive,

    requires
        child.exec_inv(),
        child.safe_inv(),
        child.productive_inv(),
        parser_congruent(child, spec_rec(())),
    ensures
        parse_matches_spec(result, cbor_body::<DET>(spec_rec).spec_parse(input@)),
{
    use crate::combinators::congruence::*;
    use crate::core::exec::bridge_lemmas::*;

    broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
    broadcast use lemma_parser_congruent_reflexive;

    let _ = input.len();
    let (head_len, head) = CborHeadFmt::<DET>.parse(input)?;
    proof {
        CborHeadFmt::<DET>.lemma_parse_safe(input@);
    }
    let rest = input.skip(head_len);

    let ghost child_spec = spec_rec(());
    proof {
        lemma_ref_parser_exec_inv::<&'i [u8], _>(child);
        lemma_ref_safe_productive_inv(child);
    }

    match head {
        CborHead { major: MajorType::Unsigned, value: CborHeadValue::Argument(value) } => {
            Ok((head_len, CborValue::Integer(value as i128)))
        },
        CborHead { major: MajorType::Negative, value: CborHeadValue::Argument(value) } => {
            Ok((head_len, CborValue::Integer(-1i128 - value as i128)))
        },
        CborHead { major: MajorType::Bytes, value: CborHeadValue::Argument(len) } => {
            let (content_len, bytes) = ExactLen(len, Tail).parse(&rest)?;
            Ok((head_len + content_len, CborValue::Bytes(CborBytes::Definite(bytes))))
        },
        CborHead { major: MajorType::Bytes, value: CborHeadValue::Indefinite } => {
            let repeated = Repeat(ByteChunkFmt::<DET>, BREAK);
            let (content_len, (chunks, _break)) = repeated.parse(&rest)?;
            let bytes = flatten_byte_chunks(chunks);
            Ok((head_len + content_len, CborValue::Bytes(CborBytes::Indefinite(bytes))))
        },
        CborHead { major: MajorType::Text, value: CborHeadValue::Argument(len) } => {
            let (content_len, text) = ExactLen(len, Utf8StringFmt).parse(&rest)?;
            Ok((head_len + content_len, CborValue::Text(CborText::Definite(text))))
        },
        CborHead { major: MajorType::Text, value: CborHeadValue::Indefinite } => {
            let repeated = Repeat(TextChunkFmt::<DET>, BREAK);
            let (content_len, (chunks, _break)) = repeated.parse(&rest)?;
            let text = flatten_text_chunks(chunks);
            Ok((head_len + content_len, CborValue::Text(CborText::Indefinite(text))))
        },
        CborHead { major: MajorType::Array, value: CborHeadValue::Argument(len) } => {
            let repeated = RepeatN(len, child);
            proof {
                lemma_repeat_n_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                lemma_repeat_n_parser_congruence(repeated, RepeatN(len, child_spec));
                lemma_parser_congruent_apply(repeated, RepeatN(len, child_spec), rest@);
            }
            let (content_len, values) = repeated.parse(&rest)?;
            let value = CborValue::Array(values);
            proof {
                super::value::lemma_collection_value_view(&value);
            }
            Ok((head_len + content_len, value))
        },
        CborHead { major: MajorType::Array, value: CborHeadValue::Indefinite } => {
            let repeated = Repeat(child, BREAK);
            proof {
                lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                lemma_repeat_parser_congruence(child, child_spec, BREAK, BREAK);
                lemma_parser_congruent_apply(repeated, Repeat(child_spec, BREAK), rest@);
            }
            let (content_len, (values, _break)) = repeated.parse(&rest)?;
            let value = CborValue::Array(values);
            proof {
                super::value::lemma_collection_value_view(&value);
            }
            Ok((head_len + content_len, value))
        },
        CborHead { major: MajorType::Map, value: CborHeadValue::Argument(len) } => {
            let entry = Pair(child, child);
            let repeated = RepeatN(len, entry);
            proof {
                lemma_pair_parser_exec_inv::<&'i [u8], _, _>(&entry);
                lemma_pair_parser_congruence(child, child_spec, child, child_spec);
                lemma_repeat_n_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                lemma_repeat_n_parser_congruence(
                    repeated,
                    RepeatN(len, Pair(child_spec, child_spec)),
                );
                lemma_parser_congruent_apply(
                    repeated,
                    RepeatN(len, Pair(child_spec, child_spec)),
                    rest@,
                );
            }
            let (content_len, entries) = repeated.parse(&rest)?;
            let value = CborValue::Map(entries);
            proof {
                super::value::lemma_collection_value_view(&value);
            }
            Ok((head_len + content_len, value))
        },
        CborHead { major: MajorType::Map, value: CborHeadValue::Indefinite } => {
            let entry = Pair(child, child);
            let repeated = Repeat(entry, BREAK);
            proof {
                lemma_pair_parser_exec_inv::<&'i [u8], _, _>(&entry);
                lemma_pair_parser_congruence(child, child_spec, child, child_spec);
                lemma_repeat_parser_exec_inv::<&'i [u8], _, _>(&repeated);
                lemma_repeat_parser_congruence(entry, Pair(child_spec, child_spec), BREAK, BREAK);
                lemma_parser_congruent_apply(
                    repeated,
                    Repeat(Pair(child_spec, child_spec), BREAK),
                    rest@,
                );
            }
            let (content_len, (entries, _break)) = repeated.parse(&rest)?;
            let value = CborValue::Map(entries);
            proof {
                super::value::lemma_collection_value_view(&value);
            }
            Ok((head_len + content_len, value))
        },
        CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(tag) } => {
            proof {
                lemma_parser_congruent_apply(child, child_spec, rest@);
            }
            let (content_len, value) = child.parse(&rest)?;
            Ok((head_len + content_len, CborValue::Tag(tag, Box::new(value))))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Float(value) } => {
            Ok((head_len, CborValue::Float(value)))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(20) } => {
            Ok((head_len, CborValue::Bool(false)))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(21) } => {
            Ok((head_len, CborValue::Bool(true)))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(22) } => {
            Ok((head_len, CborValue::Null))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(23) } => {
            Ok((head_len, CborValue::Undefined))
        },
        CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(value) } => {
            Ok((head_len, CborValue::Simple(value)))
        },
        _ => Err(ParseError::custom("invalid CBOR head/value combination")),
    }
}

fn serialize_cbor_with_child<'i, Output, const DET: bool, Exec>(
    Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
    exec_rec: Exec,
    value: &CborValue<'i>,
    out: &mut Output,
) where Output: OutputBuf, Exec: Fn(&(), &CborValue<'i>, &mut Output)
    requires
        cbor_body::<DET>(spec_rec).consistent(value.deep_view()),
        old(out).fits(cbor_body::<DET>(spec_rec).byte_len(value.deep_view())),
        forall|pp: &(), vv: &CborValue<'i>, output: &mut Output|
            {
                &&& spec_rec(pp.deep_view()).0(vv.deep_view())
                &&& output.fits(spec_rec(pp.deep_view()).1(vv.deep_view()))
            } ==> call_requires(exec_rec, (pp, vv, output)),
        forall|pp: &(), vv: &CborValue<'i>, output: &mut Output|
            call_ensures(exec_rec, (pp, vv, output), ()) ==> {
                &&& final(output)@ == output@ + spec_rec(pp.deep_view()).3(vv.deep_view())
                &&& forall|n|
                    output.fits(spec_rec(pp.deep_view()).1(vv.deep_view()) + n)
                        <==> #[trigger] final(output).fits(n)
                &&& output.same_destination(final(output))
            },
    ensures
        final(out)@ == old(out)@ + cbor_body::<DET>(spec_rec).spec_serialize(value.deep_view()),
        forall|n|
            old(out).fits(cbor_body::<DET>(spec_rec).byte_len(value.deep_view()) + n)
                <==> #[trigger] final(out).fits(n),
        old(out).same_destination(final(out)),
{
    use crate::combinators::congruence::*;
    use crate::core::exec::bridge_lemmas::*;
    broadcast use crate::core::exec::output::outbuf_lemmas;

    reveal(<crate::combinators::Star<_> as Consistency>::consistent);
    reveal(<crate::combinators::Star<_> as SpecByteLen>::byte_len);
    reveal(<crate::combinators::Star<_> as SpecSerializer>::spec_serialize);

    let ghost child_spec = spec_rec(());
    let child_exec = |child_value: &CborValue<'i>, output: &mut Output| -> ()
        requires
            child_spec.consistent(child_value.deep_view()),
            old(output).fits(child_spec.byte_len(child_value.deep_view())),
        ensures
            final(output)@ == old(output)@ + child_spec.spec_serialize(child_value.deep_view()),
            forall|n|
                old(output).fits(child_spec.byte_len(child_value.deep_view()) + n)
                    <==> #[trigger] final(output).fits(n),
            old(output).same_destination(final(output)),
        { exec_rec(&(), child_value, output) };
    let child: FnSerializer<Output, CborValue<'i>, BundledSpecs<CborValueSpec>, _> =
        FnSerializer::new(child_exec, Ghost(child_spec));
    proof {
        lemma_ref_serializer_exec_inv::<Output, _, CborValue<'i>>(&child);
        lemma_ref_fn_serializer_congruence(&child);
    }

    match value {
        CborValue::Integer(integer) => {
            let head = if *integer >= 0 {
                CborHead {
                    major: MajorType::Unsigned,
                    value: CborHeadValue::Argument(*integer as u64),
                }
            } else {
                CborHead {
                    major: MajorType::Negative,
                    value: CborHeadValue::Argument((-1i128 - *integer) as u64),
                }
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
        CborValue::Bytes(CborBytes::Definite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            Tail.serialize_into(bytes, out);
        },
        CborValue::Bytes(CborBytes::Indefinite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            Tail.serialize_into(bytes.as_slice(), out);
        },
        CborValue::Text(CborText::Definite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_bytes().len() as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            Utf8StringFmt.serialize_into(text, out);
        },
        CborValue::Text(CborText::Indefinite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_str().as_bytes().len() as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            Utf8StringFmt.serialize_into(text, out);
        },
        CborValue::Array(values) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = values.len();
            let head = CborHead {
                major: MajorType::Array,
                value: CborHeadValue::Argument(count as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            let repeated = RepeatN(count as u64, &child);
            let ghost repeated_spec = RepeatN(count as u64, child_spec);
            proof {
                lemma_repeat_n_serializer_exec_inv::<Output, _, _, CborValue<'i>>(&repeated);
                lemma_repeat_n_serializer_congruence(repeated, repeated_spec);
                lemma_serializer_congruent_prepare(repeated, repeated_spec);
                lemma_prepare_congruent_consistent(repeated, repeated_spec, values.deep_view());
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, values.deep_view());
                lemma_serializer_congruent_serialize(repeated, repeated_spec, values.deep_view());
            }
            repeated.serialize_into(values.as_slice(), out);
        },
        CborValue::Map(entries) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = entries.len();
            let head = CborHead {
                major: MajorType::Map,
                value: CborHeadValue::Argument(count as u64),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
            let entry = Pair(&child, &child);
            let ghost entry_spec = Pair(child_spec, child_spec);
            let repeated = RepeatN(count as u64, entry);
            let ghost repeated_spec = RepeatN(count as u64, entry_spec);
            proof {
                lemma_pair_serializer_congruence(entry, entry_spec);
                lemma_pair_serializer_exec_inv::<Output, _, _, CborValue<'i>, CborValue<'i>>(
                    &entry,
                );
                lemma_repeat_n_serializer_exec_inv::<Output, _, _, (CborValue<'i>, CborValue<'i>)>(
                    &repeated,
                );
                lemma_repeat_n_serializer_congruence(repeated, repeated_spec);
                lemma_serializer_congruent_prepare(repeated, repeated_spec);
                lemma_prepare_congruent_consistent(repeated, repeated_spec, entries.deep_view());
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, entries.deep_view());
                lemma_serializer_congruent_serialize(repeated, repeated_spec, entries.deep_view());
            }
            repeated.serialize_into(entries.as_slice(), out);
        },
        CborValue::Tag(tag, inner) => {
            let head = CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(*tag) };
            proof {
                assert(child_spec.consistent((**inner).deep_view()));
                lemma_serializer_congruent_prepare(&child, child_spec);
                lemma_prepare_congruent_consistent(&child, child_spec, (**inner).deep_view());
                lemma_prepare_congruent_byte_len(&child, child_spec, (**inner).deep_view());
                lemma_serializer_congruent_serialize(&child, child_spec, (**inner).deep_view());
                lemma_fn_serializer_specs(&child, (**inner).deep_view());
            }
            CborHeadFmt::<DET>.serialize_into(&head, out);
            child.serialize_into(&**inner, out);
        },
        CborValue::Float(float) => {
            let head = CborHead { major: MajorType::Simple, value: CborHeadValue::Float(*float) };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
        CborValue::Bool(boolean) => {
            let head = CborHead {
                major: MajorType::Simple,
                value: CborHeadValue::Simple(
                    if *boolean {
                        21
                    } else {
                        20
                    },
                ),
            };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
        CborValue::Null => {
            let head = CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(22) };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
        CborValue::Undefined => {
            let head = CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(23) };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
        CborValue::Simple(simple) => {
            let head = CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(*simple) };
            CborHeadFmt::<DET>.serialize_into(&head, out);
        },
    }
}

fn checked_add_lengths(left: usize, right: usize) -> (result: Result<usize, PreSerializeError>)
    ensures
        result matches Ok(total) ==> total as nat == left as nat + right as nat,
{
    match left.checked_add(right) {
        Some(total) => Ok(total),
        None => Err(PreSerializeError::length_too_large()),
    }
}

fn prepare_cbor_with_child<'i, const DET: bool, Exec>(
    Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
    exec_rec: Exec,
    value: &CborValue<'i>,
) -> (result: Result<usize, PreSerializeError>) where
    Exec: Fn(&(), &CborValue<'i>) -> Result<usize, PreSerializeError>,

    requires
        forall|pp: &(), vv: &CborValue<'i>| call_requires(exec_rec, (pp, vv)),
        forall|pp: &(), vv: &CborValue<'i>, rr: Result<usize, PreSerializeError>|
            call_ensures(exec_rec, (pp, vv), rr) ==> (rr matches Ok(len) ==> {
                &&& spec_rec(pp.deep_view()).0(vv.deep_view())
                &&& len == spec_rec(pp.deep_view()).1(vv.deep_view())
            }),
    ensures
        result matches Ok(len) ==> {
            &&& cbor_body::<DET>(spec_rec).consistent(value.deep_view())
            &&& len == cbor_body::<DET>(spec_rec).byte_len(value.deep_view())
        },
{
    use crate::combinators::congruence::*;
    use crate::core::exec::bridge_lemmas::*;

    let ghost child_spec = spec_rec(());
    let child_exec = |child_value: &CborValue<'i>| -> (child_result: Result<
        usize,
        PreSerializeError,
    >)
        ensures
            child_result matches Ok(len) ==> {
                &&& child_spec.consistent(child_value.deep_view())
                &&& len == child_spec.byte_len(child_value.deep_view())
            },
        { exec_rec(&(), child_value) };
    let child: FnPrepare<CborValue<'i>, BundledSpecs<CborValueSpec>, _> = FnPrepare::new(
        child_exec,
        Ghost(child_spec),
    );
    proof {
        lemma_ref_prepare_exec_inv(&child);
        lemma_ref_fn_prepare_congruence(&child);
    }

    match value {
        CborValue::Integer(integer) => {
            if *integer < -1i128 - u64::MAX as i128 || *integer > u64::MAX as i128 {
                return Err(PreSerializeError::custom("CBOR integer is out of range"));
            }
            let head = if *integer >= 0 {
                CborHead {
                    major: MajorType::Unsigned,
                    value: CborHeadValue::Argument(*integer as u64),
                }
            } else {
                CborHead {
                    major: MajorType::Negative,
                    value: CborHeadValue::Argument((-1i128 - *integer) as u64),
                }
            };
            CborHeadFmt::<DET>.prepare(&head)
        },
        CborValue::Bytes(CborBytes::Definite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = Tail.prepare(bytes)?;
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Bytes(CborBytes::Indefinite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = Tail.prepare(bytes.as_slice())?;
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Text(CborText::Definite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_bytes().len() as u64),
            };
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = Utf8StringFmt.prepare(text)?;
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Text(CborText::Indefinite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_str().as_bytes().len() as u64),
            };
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = Utf8StringFmt.prepare(text)?;
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Array(values) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = values.len();
            let head = CborHead {
                major: MajorType::Array,
                value: CborHeadValue::Argument(count as u64),
            };
            let repeated = RepeatN(count as u64, &child);
            let ghost repeated_spec = RepeatN(count as u64, child_spec);
            proof {
                lemma_repeat_n_prepare_exec_inv::<_, _, CborValue<'i>>(&repeated);
                lemma_repeat_n_prepare_congruence(repeated, repeated_spec);
            }
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = repeated.prepare(values.as_slice())?;
            proof {
                lemma_prepare_congruent_consistent(repeated, repeated_spec, values.deep_view());
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, values.deep_view());
            }
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Map(entries) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = entries.len();
            let head = CborHead {
                major: MajorType::Map,
                value: CborHeadValue::Argument(count as u64),
            };
            let entry = Pair(&child, &child);
            let ghost entry_spec = Pair(child_spec, child_spec);
            let repeated = RepeatN(count as u64, entry);
            let ghost repeated_spec = RepeatN(count as u64, entry_spec);
            proof {
                lemma_pair_prepare_exec_inv::<_, _, CborValue<'i>, CborValue<'i>>(&entry);
                lemma_pair_prepare_congruence(entry, entry_spec);
                lemma_repeat_n_prepare_exec_inv::<_, _, (CborValue<'i>, CborValue<'i>)>(&repeated);
                lemma_repeat_n_prepare_congruence(repeated, repeated_spec);
            }
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = repeated.prepare(entries.as_slice())?;
            proof {
                lemma_prepare_congruent_consistent(repeated, repeated_spec, entries.deep_view());
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, entries.deep_view());
            }
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Tag(tag, inner) => {
            let head = CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(*tag) };
            let head_len = CborHeadFmt::<DET>.prepare(&head)?;
            let content_len = child.prepare(&**inner)?;
            proof {
                lemma_prepare_congruent_consistent(&child, child_spec, (**inner).deep_view());
                lemma_prepare_congruent_byte_len(&child, child_spec, (**inner).deep_view());
                lemma_fn_prepare_specs(&child, (**inner).deep_view());
            }
            checked_add_lengths(head_len, content_len)
        },
        CborValue::Float(float) => CborHeadFmt::<DET>.prepare(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Float(*float) },
        ),
        CborValue::Bool(boolean) => CborHeadFmt::<DET>.prepare(
            &CborHead {
                major: MajorType::Simple,
                value: CborHeadValue::Simple(
                    if *boolean {
                        21
                    } else {
                        20
                    },
                ),
            },
        ),
        CborValue::Null => CborHeadFmt::<DET>.prepare(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(22) },
        ),
        CborValue::Undefined => CborHeadFmt::<DET>.prepare(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(23) },
        ),
        CborValue::Simple(simple) => {
            if *simple > 19 && *simple < 32 {
                Err(PreSerializeError::custom("reserved CBOR simple value"))
            } else {
                CborHeadFmt::<DET>.prepare(
                    &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(*simple) },
                )
            }
        },
    }
}

fn length_cbor_with_child<'i, const DET: bool, Exec>(
    Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
    exec_rec: Exec,
    value: &CborValue<'i>,
) -> (len: usize) where Exec: Fn(&(), &CborValue<'i>) -> usize
    requires
        cbor_body::<DET>(spec_rec).byte_len(value.deep_view()) <= usize::MAX,
        forall|pp: &(), vv: &CborValue<'i>|
            spec_rec(pp.deep_view()).1(vv.deep_view()) <= usize::MAX ==> call_requires(
                exec_rec,
                (pp, vv),
            ),
        forall|pp: &(), vv: &CborValue<'i>, child_len: usize|
            call_ensures(exec_rec, (pp, vv), child_len) ==> child_len == spec_rec(pp.deep_view()).1(
                vv.deep_view(),
            ),
    ensures
        len == cbor_body::<DET>(spec_rec).byte_len(value.deep_view()),
{
    use crate::combinators::congruence::*;
    use crate::core::exec::bridge_lemmas::*;

    let ghost child_spec = spec_rec(());
    let child_exec = |child_value: &CborValue<'i>| -> (child_len: usize)
        requires
            child_spec.byte_len(child_value.deep_view()) <= usize::MAX,
        ensures
            child_len == child_spec.byte_len(child_value.deep_view()),
        { exec_rec(&(), child_value) };
    let child: FnByteLen<CborValue<'i>, BundledSpecs<CborValueSpec>, _> = FnByteLen::new(
        child_exec,
        Ghost(child_spec),
    );
    proof {
        lemma_ref_fn_byte_len_congruence(&child);
        lemma_ref_byte_len_exec_inv::<_, CborValue<'i>>(&child);
    }

    match value {
        CborValue::Integer(integer) => {
            let head = if *integer >= 0 {
                CborHead {
                    major: MajorType::Unsigned,
                    value: CborHeadValue::Argument(*integer as u64),
                }
            } else {
                CborHead {
                    major: MajorType::Negative,
                    value: CborHeadValue::Argument((-1i128 - *integer) as u64),
                }
            };
            CborHeadFmt::<DET>.length(&head)
        },
        CborValue::Bytes(CborBytes::Definite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            CborHeadFmt::<DET>.length(&head) + Tail.length(bytes)
        },
        CborValue::Bytes(CborBytes::Indefinite(bytes)) => {
            let head = CborHead {
                major: MajorType::Bytes,
                value: CborHeadValue::Argument(bytes.len() as u64),
            };
            CborHeadFmt::<DET>.length(&head) + Tail.length(bytes.as_slice())
        },
        CborValue::Text(CborText::Definite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_bytes().len() as u64),
            };
            CborHeadFmt::<DET>.length(&head) + Utf8StringFmt.length(text)
        },
        CborValue::Text(CborText::Indefinite(text)) => {
            let head = CborHead {
                major: MajorType::Text,
                value: CborHeadValue::Argument(text.as_str().as_bytes().len() as u64),
            };
            CborHeadFmt::<DET>.length(&head) + Utf8StringFmt.length(text)
        },
        CborValue::Array(values) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = values.len();
            let head = CborHead {
                major: MajorType::Array,
                value: CborHeadValue::Argument(count as u64),
            };
            let repeated = RepeatN(count as u64, &child);
            let ghost repeated_spec = RepeatN(count as u64, child_spec);
            proof {
                lemma_repeat_n_prepare_congruence(repeated, repeated_spec);
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, values.deep_view());
                lemma_repeat_n_byte_len_exec_inv::<_, _, CborValue<'i>>(&repeated);
            }
            CborHeadFmt::<DET>.length(&head) + repeated.length(values.as_slice())
        },
        CborValue::Map(entries) => {
            proof {
                super::value::lemma_collection_value_view(value);
            }
            let count = entries.len();
            let head = CborHead {
                major: MajorType::Map,
                value: CborHeadValue::Argument(count as u64),
            };
            let entry = Pair(&child, &child);
            let ghost entry_spec = Pair(child_spec, child_spec);
            let repeated = RepeatN(count as u64, entry);
            let ghost repeated_spec = RepeatN(count as u64, entry_spec);
            proof {
                lemma_pair_prepare_congruence(entry, entry_spec);
                lemma_repeat_n_prepare_congruence(repeated, repeated_spec);
                lemma_prepare_congruent_byte_len(repeated, repeated_spec, entries.deep_view());
                lemma_pair_byte_len_exec_inv::<_, _, CborValue<'i>, CborValue<'i>>(&entry);
                lemma_repeat_n_byte_len_exec_inv::<_, _, (CborValue<'i>, CborValue<'i>)>(&repeated);
            }
            CborHeadFmt::<DET>.length(&head) + repeated.length(entries.as_slice())
        },
        CborValue::Tag(tag, inner) => {
            proof {
                lemma_prepare_congruent_byte_len(&child, child_spec, (**inner).deep_view());
                lemma_fn_byte_len_specs(&child, (**inner).deep_view());
            }
            let head = CborHead { major: MajorType::Tag, value: CborHeadValue::Argument(*tag) };
            CborHeadFmt::<DET>.length(&head) + child.length(&**inner)
        },
        CborValue::Float(float) => CborHeadFmt::<DET>.length(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Float(*float) },
        ),
        CborValue::Bool(boolean) => CborHeadFmt::<DET>.length(
            &CborHead {
                major: MajorType::Simple,
                value: CborHeadValue::Simple(
                    if *boolean {
                        21
                    } else {
                        20
                    },
                ),
            },
        ),
        CborValue::Null => CborHeadFmt::<DET>.length(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(22) },
        ),
        CborValue::Undefined => CborHeadFmt::<DET>.length(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(23) },
        ),
        CborValue::Simple(simple) => CborHeadFmt::<DET>.length(
            &CborHead { major: MajorType::Simple, value: CborHeadValue::Simple(*simple) },
        ),
    }
}

fn cbor_length_gas<'i, const DET: bool, const LIMIT: usize>(
    gas: usize,
    value: &CborValue<'i>,
) -> (len: usize)
    requires
        FixWith::<LIMIT, CborRecBody<DET>, ()>::byte_len_gas(
            &CborRecBody::<DET>,
            gas as nat,
            (),
            value.deep_view(),
        ) <= usize::MAX,
    ensures
        len == FixWith::<LIMIT, CborRecBody<DET>, ()>::byte_len_gas(
            &CborRecBody::<DET>,
            gas as nat,
            (),
            value.deep_view(),
        ),
    decreases gas,
{
    let ghost body = CborRecBody::<DET>;
    let ghost spec_rec = FixWith::<LIMIT, CborRecBody<DET>, ()>::specs_callback(&body, gas as nat);
    let exec_rec = |_param: &(), child: &CborValue<'i>| -> (child_len: usize)
        requires
            spec_rec(()).byte_len(child.deep_view()) <= usize::MAX,
        ensures
            child_len == spec_rec(()).byte_len(child.deep_view()),
        {
            if gas > 0 {
                cbor_length_gas::<DET, LIMIT>((gas - 1) as usize, child)
            } else {
                0
            }
        };
    length_cbor_with_child::<DET, _>(Ghost(spec_rec), exec_rec, value)
}

fn parse_cbor_rec_body<'i, const DET: bool, Exec>(
    param: &(),
    Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
    exec_rec: Exec,
    input: &&'i [u8],
) -> (result: PResult<CborValue<'i>>) where Exec: Fn(&(), &&'i [u8]) -> PResult<CborValue<'i>>
    requires
        forall|p: ()| #[trigger] spec_rec(p).safe_inv(),
        forall|p: ()| #[trigger] spec_rec(p).productive_inv(),
        forall|pp: &(), i: &&'i [u8]| call_requires(exec_rec, (pp, i)),
        forall|pp: &(), i: &&'i [u8], rr: PResult<CborValue<'i>>|
            call_ensures(exec_rec, (pp, i), rr) ==> parse_matches_spec(
                rr,
                spec_rec(pp.deep_view()).2(i@),
            ),
    ensures
        parse_matches_spec(result, cbor_body::<DET>(spec_rec).spec_parse(input@)),
{
    let ghost child_spec = spec_rec(());
    let child_exec = |child_input: &&'i [u8]| -> (result: PResult<CborValue<'i>>)
        ensures
            parse_matches_spec(result, child_spec.2(child_input@)),
        { exec_rec(param, child_input) };
    let child: FnParser<&'i [u8], CborValue<'i>, BundledSpecs<CborValueSpec>, _> = FnParser::new(
        child_exec,
        Ghost(child_spec),
    );
    proof {
        crate::combinators::congruence::lemma_ref_fn_parser_congruence(&child);
    }
    parse_cbor_with_child::<DET, _>(Ghost(spec_rec), &child, input)
}

// Verus currently loses the inherited higher-order `Exec` contract on a const-generic
// `ParserRecBody` impl. Keep only these mode-specific trait shims; all logic remains in the
// const-generic helper above.
impl<'i> ParserRecBody<&'i [u8]> for CborRecBody<false> where
    CborRecBody<false>: SpecRecBody<Param = (), T = CborValueSpec, Body = CborBodyFmt<false>>,
 {
    type EP = ();

    type O = CborValue<'i>;

    fn parse_body<Exec>(
        &self,
        param: &(),
        spec_rec: Ghost<ParamRecSpecs<(), CborValueSpec>>,
        exec_rec: Exec,
        input: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&(), &&'i [u8]) -> PResult<Self::O> {
        parse_cbor_rec_body::<false, _>(param, spec_rec, exec_rec, input)
    }
}

impl<'i> ParserRecBody<&'i [u8]> for CborRecBody<true> where
    CborRecBody<true>: SpecRecBody<Param = (), T = CborValueSpec, Body = CborBodyFmt<true>>,
 {
    type EP = ();

    type O = CborValue<'i>;

    fn parse_body<Exec>(
        &self,
        param: &(),
        spec_rec: Ghost<ParamRecSpecs<(), CborValueSpec>>,
        exec_rec: Exec,
        input: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&(), &&'i [u8]) -> PResult<Self::O> {
        parse_cbor_rec_body::<true, _>(param, spec_rec, exec_rec, input)
    }
}

impl<'i, Output: OutputBuf, const DET: bool> SerializerRecBody<
    Output,
    CborValue<'i>,
> for CborRecBody<DET> {
    type EP = ();

    fn serialize_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<(), CborValueSpec>>,
        exec_rec: Exec,
        value: &CborValue<'i>,
        out: &mut Output,
    ) where Exec: Fn(&(), &CborValue<'i>, &mut Output) {
        serialize_cbor_with_child::<Output, DET, _>(Ghost(spec_rec), exec_rec, value, out)
    }
}

// The corresponding const-generic `PrepareRecBody` impl has the same Verus callback-contract
// limitation. Both shims delegate to `prepare_cbor_with_child`.
impl<'i> PrepareRecBody<CborValue<'i>> for CborRecBody<false> where
    CborRecBody<false>: SpecRecBody<Param = (), T = CborValueSpec, Body = CborBodyFmt<false>>,
 {
    type EP = ();

    fn prepare_body<Exec>(
        &self,
        _param: &(),
        spec_rec: Ghost<ParamRecSpecs<(), CborValueSpec>>,
        exec_rec: Exec,
        value: &CborValue<'i>,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&(), &CborValue<'i>) -> Result<usize, PreSerializeError>,
     {
        prepare_cbor_with_child::<false, _>(spec_rec, exec_rec, value)
    }
}

impl<'i> PrepareRecBody<CborValue<'i>> for CborRecBody<true> where
    CborRecBody<true>: SpecRecBody<Param = (), T = CborValueSpec, Body = CborBodyFmt<true>>,
 {
    type EP = ();

    fn prepare_body<Exec>(
        &self,
        _param: &(),
        spec_rec: Ghost<ParamRecSpecs<(), CborValueSpec>>,
        exec_rec: Exec,
        value: &CborValue<'i>,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&(), &CborValue<'i>) -> Result<usize, PreSerializeError>,
     {
        prepare_cbor_with_child::<true, _>(spec_rec, exec_rec, value)
    }
}

/// A complete generic CBOR data item with bounded nesting.
#[derive(Clone, Copy)]
pub struct CborFmt<const DET: bool, const LIMIT: usize = MAX_RECURSION_DEPTH>;

pub open spec fn cbor_fmt<const DET: bool, const LIMIT: usize>() -> FixWith<
    LIMIT,
    CborRecBody<DET>,
    (),
> {
    FixWith(CborRecBody::<DET>, ())
}

impl<'i, const DET: bool, const LIMIT: usize> Parser<&'i [u8]> for CborFmt<DET, LIMIT> where
    CborRecBody<DET>: SpecRecBody<
        Param = (),
        T = CborValueSpec,
        Body = CborBodyFmt<DET>,
    > + ParserRecBody<&'i [u8], EP = (), O = CborValue<'i>>,
    <CborRecBody<DET> as SpecRecBody>::Body: Productive,
 {
    type PT = CborValue<'i>;

    fn parse(&self, input: &&'i [u8]) -> PResult<Self::PT> {
        FixWith::<LIMIT, _, _>(CborRecBody::<DET>, ()).parse(input)
    }
}

impl<'i, Output: OutputBuf, const DET: bool, const LIMIT: usize> Serializer<
    Output,
    CborValue<'i>,
> for CborFmt<DET, LIMIT> {
    fn serialize_into(&self, value: &CborValue<'i>, out: &mut Output) {
        FixWith::<LIMIT, _, _>(CborRecBody::<DET>, ()).serialize_into(value, out)
    }
}

impl<'i, const DET: bool, const LIMIT: usize> Prepare<CborValue<'i>> for CborFmt<DET, LIMIT> where
    CborRecBody<DET>: SpecRecBody<
        Param = (),
        T = CborValueSpec,
        Body = CborBodyFmt<DET>,
    > + PrepareRecBody<CborValue<'i>, EP = ()>,
 {
    fn prepare(&self, value: &CborValue<'i>) -> Result<usize, PreSerializeError> {
        FixWith::<LIMIT, _, _>(CborRecBody::<DET>, ()).prepare(value)
    }
}

impl<'i, const DET: bool, const LIMIT: usize> ByteLen<CborValue<'i>> for CborFmt<DET, LIMIT> {
    fn length(&self, value: &CborValue<'i>) -> usize {
        cbor_length_gas::<DET, LIMIT>(LIMIT, value)
    }
}

mod derived_specs {
    use super::*;

    impl<const DET: bool> SpecParser for CborBodyFmt<DET> {
        type PVal = CborValueSpec;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            cbor_parse_body::<DET>(self.rec@).spec_parse(input)
        }
    }

    impl<const DET: bool> Consistency for CborBodyFmt<DET> {
        type Val = CborValueSpec;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            cbor_normalized_body::<DET>(self.rec@).consistent(value)
        }
    }

    impl<const DET: bool> SpecSerializerDps for CborBodyFmt<DET> {
        type SValue = CborValueSpec;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            cbor_normalized_body::<DET>(self.rec@).spec_serialize_dps(value, out)
        }
    }

    impl<const DET: bool> SpecSerializer for CborBodyFmt<DET> {
        type SVal = CborValueSpec;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            cbor_normalized_body::<DET>(self.rec@).spec_serialize(value)
        }
    }

    impl<const DET: bool> SpecByteLen for CborBodyFmt<DET> {
        type T = CborValueSpec;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            cbor_normalized_body::<DET>(self.rec@).byte_len(value)
        }
    }

    impl<const DET: bool, const LIMIT: usize> SpecParser for CborFmt<DET, LIMIT> {
        type PVal = CborValueSpec;

        open spec fn spec_parse(&self, input: Seq<u8>) -> Option<(int, Self::PVal)> {
            cbor_fmt::<DET, LIMIT>().spec_parse(input)
        }
    }

    impl<const DET: bool, const LIMIT: usize> Consistency for CborFmt<DET, LIMIT> {
        type Val = CborValueSpec;

        open spec fn consistent(&self, value: Self::Val) -> bool {
            cbor_fmt::<DET, LIMIT>().consistent(value)
        }
    }

    impl<const DET: bool, const LIMIT: usize> SpecSerializerDps for CborFmt<DET, LIMIT> {
        type SValue = CborValueSpec;

        open spec fn spec_serialize_dps(&self, value: Self::SValue, out: Seq<u8>) -> Seq<u8> {
            cbor_fmt::<DET, LIMIT>().spec_serialize_dps(value, out)
        }
    }

    impl<const DET: bool, const LIMIT: usize> SpecSerializer for CborFmt<DET, LIMIT> {
        type SVal = CborValueSpec;

        open spec fn spec_serialize(&self, value: Self::SVal) -> Seq<u8> {
            cbor_fmt::<DET, LIMIT>().spec_serialize(value)
        }
    }

    impl<const DET: bool, const LIMIT: usize> SpecByteLen for CborFmt<DET, LIMIT> {
        type T = CborValueSpec;

        open spec fn byte_len(&self, value: Self::T) -> nat {
            cbor_fmt::<DET, LIMIT>().byte_len(value)
        }
    }

}

mod recursive_proofs {
    use super::*;

    impl<const DET: bool> SafeParserRecBody for CborRecBody<DET> {
        proof fn lemma_body_safe_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl<const DET: bool> ProductiveRecBody for CborRecBody<DET> {
        proof fn lemma_body_productive_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl SoundParserRecBody for CborRecBody<true> {
        proof fn lemma_body_sound_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl NonMalleableRecBody for CborRecBody<true> {
        proof fn lemma_body_nonmal_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl<const DET: bool> GoodSerializerRecBody for CborRecBody<DET> {
        proof fn lemma_s_body_serialize_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl<const DET: bool> NonTailFmtRecBody for CborRecBody<DET> {
        proof fn lemma_s_body_dps_serialize_dps_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl<const DET: bool> SPRoundTripDpsRecBody for CborRecBody<DET> {
        proof fn lemma_body_sp_roundtrip_dps_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

    impl<const DET: bool> EquivSerializersGeneralRecBody for CborRecBody<DET> {
        proof fn lemma_s_body_equiv_general_inv_preservation(
            &self,
            _param: (),
            _rec: ParamRecSpecs<(), CborValueSpec>,
        ) {
        }
    }

}

mod derived_proofs {
    use super::*;

    impl<const DET: bool> SafeParser for CborBodyFmt<DET> {
        open spec fn safe_inv(&self) -> bool {
            cbor_parse_body::<DET>(self.rec@).safe_inv()
        }

        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            cbor_parse_body::<DET>(self.rec@).lemma_parse_safe(input);
        }
    }

    impl<const DET: bool> Productive for CborBodyFmt<DET> {
        open spec fn productive_inv(&self) -> bool {
            cbor_parse_body::<DET>(self.rec@).productive_inv()
        }

        proof fn lemma_productive(&self, input: Seq<u8>) {
            cbor_parse_body::<DET>(self.rec@).lemma_productive(input);
        }
    }

    impl SoundParser for CborBodyFmt<true> {
        open spec fn sound_inv(&self) -> bool {
            cbor_parse_body::<true>(self.rec@).sound_inv()
        }

        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            cbor_parse_body::<true>(self.rec@).lemma_parse_sound_consumption(input);
            if let Some((_n, value)) = self.spec_parse(input) {
                lemma_parse_normalized_byte_len::<true>(self.rec@, value);
            }
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            cbor_parse_body::<true>(self.rec@).lemma_parse_sound_value(input);
            if let Some((_n, value)) = self.spec_parse(input) {
                lemma_parse_normalized_consistency::<true>(self.rec@, value);
            }
        }
    }

    impl<const DET: bool> GoodSerializer for CborBodyFmt<DET> {
        open spec fn serialize_inv(&self) -> bool {
            cbor_normalized_body::<DET>(self.rec@).serialize_inv()
        }

        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            cbor_normalized_body::<DET>(self.rec@).lemma_serialize_len(value);
        }
    }

    impl<const DET: bool> NonTailFmt for CborBodyFmt<DET> {
        open spec fn serialize_dps_inv(&self) -> bool {
            cbor_normalized_body::<DET>(self.rec@).serialize_dps_inv()
        }

        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_normalized_body::<DET>(self.rec@).lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_normalized_body::<DET>(self.rec@).lemma_serialize_dps_len(value, out);
        }
    }

    impl<const DET: bool> SPRoundTripDps for CborBodyFmt<DET> {
        open spec fn unambiguous(&self) -> bool {
            cbor_normalized_body::<DET>(self.rec@).unambiguous()
        }

        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            let normalized = cbor_normalized_body::<DET>(self.rec@);
            normalized.theorem_serialize_dps_parse_roundtrip(value, out);
            lemma_normalized_parse_implies_parse::<DET>(
                self.rec@,
                normalized.spec_serialize_dps(value, out),
            );
        }
    }

    impl NonMalleable for CborBodyFmt<true> {
        open spec fn nonmal_inv(&self) -> bool {
            cbor_parse_body::<true>(self.rec@).nonmal_inv()
        }

        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            cbor_parse_body::<true>(self.rec@).lemma_parse_non_malleable(left, right);
        }
    }

    impl<const DET: bool> EquivSerializersGeneral for CborBodyFmt<DET> {
        open spec fn equiv_general_inv(&self) -> bool {
            cbor_normalized_body::<DET>(self.rec@).equiv_general_inv()
        }

        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            cbor_normalized_body::<DET>(self.rec@).lemma_serialize_equiv(value, out);
        }
    }

    impl<const DET: bool> EquivSerializers for CborBodyFmt<DET> {
        open spec fn equiv_inv(&self) -> bool {
            cbor_normalized_body::<DET>(self.rec@).equiv_inv()
        }

        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            cbor_normalized_body::<DET>(self.rec@).lemma_serialize_equiv_on_empty(value);
        }
    }

    impl<const DET: bool, const LIMIT: usize> SafeParser for CborFmt<DET, LIMIT> {
        proof fn lemma_parse_safe(&self, input: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().lemma_parse_safe(input);
        }
    }

    impl<const DET: bool, const LIMIT: usize> Productive for CborFmt<DET, LIMIT> {
        proof fn lemma_productive(&self, input: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().lemma_productive(input);
        }
    }

    impl<const LIMIT: usize> SoundParser for CborFmt<true, LIMIT> {
        proof fn lemma_parse_sound_consumption(&self, input: Seq<u8>) {
            cbor_fmt::<true, LIMIT>().lemma_parse_sound_consumption(input);
        }

        proof fn lemma_parse_sound_value(&self, input: Seq<u8>) {
            cbor_fmt::<true, LIMIT>().lemma_parse_sound_value(input);
        }
    }

    impl<const DET: bool, const LIMIT: usize> GoodSerializer for CborFmt<DET, LIMIT> {
        proof fn lemma_serialize_len(&self, value: Self::SVal) {
            cbor_fmt::<DET, LIMIT>().lemma_serialize_len(value);
        }
    }

    impl<const DET: bool, const LIMIT: usize> NonTailFmt for CborFmt<DET, LIMIT> {
        proof fn lemma_serialize_dps_prepend(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().lemma_serialize_dps_prepend(value, out);
        }

        proof fn lemma_serialize_dps_len(&self, value: Self::SValue, out: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().lemma_serialize_dps_len(value, out);
        }
    }

    impl<const DET: bool, const LIMIT: usize> SPRoundTripDps for CborFmt<DET, LIMIT> {
        proof fn theorem_serialize_dps_parse_roundtrip(&self, value: Self::T, out: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().theorem_serialize_dps_parse_roundtrip(value, out);
        }
    }

    impl<const LIMIT: usize> NonMalleable for CborFmt<true, LIMIT> {
        proof fn lemma_parse_non_malleable(&self, left: Seq<u8>, right: Seq<u8>) {
            cbor_fmt::<true, LIMIT>().lemma_parse_non_malleable(left, right);
        }
    }

    impl<const DET: bool, const LIMIT: usize> EquivSerializersGeneral for CborFmt<DET, LIMIT> {
        proof fn lemma_serialize_equiv(&self, value: Self::SVal, out: Seq<u8>) {
            cbor_fmt::<DET, LIMIT>().lemma_serialize_equiv(value, out);
        }
    }

    impl<const DET: bool, const LIMIT: usize> EquivSerializers for CborFmt<DET, LIMIT> {
        proof fn lemma_serialize_equiv_on_empty(&self, value: Self::SVal) {
            cbor_fmt::<DET, LIMIT>().lemma_serialize_equiv_on_empty(value);
        }
    }

}

} // verus!
