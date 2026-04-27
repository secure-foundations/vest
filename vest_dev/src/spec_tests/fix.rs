use crate::combinators::mapped;
use crate::combinators::mapped::exec::*;
use crate::combinators::mapped::spec::*;
use crate::combinators::recursive::exec::*;
use crate::combinators::recursive::*;
use crate::combinators::*;
use crate::core::exec::fns;
use crate::core::exec::input::InputBuf;
use crate::core::exec::parser::*;
use crate::core::exec::serializer::*;
use crate::core::proof::*;
use crate::core::spec::*;
use vest_derive::DeepView;
use vstd::prelude::*;

verus! {

/*
* Example recursive parser: nested braces
*/
/// Example recursive value type: nested braces `{...}` or empty `\0`.
#[derive(Debug, DeepView)]
pub enum NestedBracesT {
    /// A brace-wrapped recursive value: `'{' inner '}'`.
    Brace(Box<NestedBracesT>),
    /// The empty (base case) value: `'\0'`.
    Eps,
}

/// Mapper between `Sum<NestedBracesT, u8>` and `NestedBracesT`.
pub struct NestedBracesMap;

pub struct NestedBracesMapRev;

impl SpecMap for NestedBracesMap {
    type SpecI = Sum<NestedBracesTSpec, u8>;

    type SpecO = NestedBracesTSpec;

    open spec fn spec_map(&self, i: Self::SpecI) -> Self::SpecO {
        match i {
            Sum::Inl(inner) => NestedBracesTSpec::Brace(Box::new(inner)),
            Sum::Inr(_) => NestedBracesTSpec::Eps,
        }
    }
}

impl fns::Map<Sum<NestedBracesT, u8>> for NestedBracesMap {
    type O = NestedBracesT;

    fn map(&self, i: Sum<NestedBracesT, u8>) -> Self::O {
        match i {
            Sum::Inl(inner) => NestedBracesT::Brace(Box::new(inner)),
            Sum::Inr(_) => NestedBracesT::Eps,
        }
    }
}

impl SpecMap for NestedBracesMapRev {
    type SpecI = NestedBracesTSpec;

    type SpecO = Sum<NestedBracesTSpec, u8>;

    open spec fn spec_map(&self, o: Self::SpecI) -> Self::SpecO {
        match o {
            NestedBracesTSpec::Brace(inner) => Sum::Inl(*inner),
            NestedBracesTSpec::Eps => Sum::Inr(0x00u8),
        }
    }
}

impl<'s> fns::Map<&'s NestedBracesT> for NestedBracesMapRev {
    type O = Sum<&'s NestedBracesT, u8>;

    fn map(&self, o: &'s NestedBracesT) -> Sum<&'s NestedBracesT, u8> {
        match o {
            NestedBracesT::Brace(inner) => Sum::Inl(&**inner),
            NestedBracesT::Eps => Sum::Inr(0x00u8),
        }
    }
}

/// One level of the nested-braces format: `'{' rec '}' | '\0'`.
// pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec>
#[verifier::allow_in_spec]
pub fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec>
    returns
        (Mapped {
            inner: Choice(
                WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U8, 0x7Bu8, rec)),
                Tag { inner: U8, tag: 0x00u8 },
            ),
            mapper: BiMap(NestedBracesMap, NestedBracesMapRev),
        }),
{
    Mapped {
        inner: Choice(
            WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U8, 0x7Bu8, rec)),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: BiMap(NestedBracesMap, NestedBracesMapRev),
    }
}

type NestedBracesBodyComb<Rec> = Mapped<
    Choice<WithSuffixTag<U8, WithPrefixTag<U8, Rec>>, Tag<U8, u8>>,
    BiMap<NestedBracesMap, NestedBracesMapRev>,
>;

/// [`SpecRecBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl SpecRecBody for NestedBracesBody {
    type T = NestedBracesTSpec;

    type Body = NestedBracesBodyComb<BundledSpecs<Self::T>>;

    open spec fn spec_body(rec: BundledSpecs<Self::T>) -> Self::Body {
        nested_braces_body(rec)
    }
}

impl<'i> ParserRecBody<&'i [u8]> for NestedBracesBody {
    type O = NestedBracesT;

    fn parse_body<Exec>(
        &self,
        spec_rec: Ghost<BundledSpecs<Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&&'i [u8]) -> PResult<Self::O> {
        let rec = fns::FnParser::new(exec_rec, spec_rec);
        let body = nested_braces_body(rec);
        body.parse(ibuf)
    }
}

impl<'s> SerializerRecBody<&'s NestedBracesT> for NestedBracesBody {
    fn serialize_body<Exec>(
        &self,
        spec_rec: Ghost<BundledSpecs<Self::T>>,
        exec_rec: Exec,
        v: &'s NestedBracesT,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&'s NestedBracesT) -> Vec<u8> {
        let rec = fns::FnSerializer::new(exec_rec, spec_rec);
        let body = nested_braces_body(rec);
        body.ex_serialize(v, obuf);
    }
}

impl StrictRecBody for NestedBracesBody {
    proof fn lemma_body_all_inv_preservation(rec: BundledSpecs<Self::T>) {
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesTSpec::Brace(Box::new(NestedBracesTSpec::Eps))),
    )) by {
        let cb = Fix::<10, NestedBracesBody>::specs_callback(10);
        let body10 = nested_braces_body(cb);
        assert(body10.spec_parse(input) == Some(
            (3int, NestedBracesTSpec::Brace(Box::new(NestedBracesTSpec::Eps))),
        ));
    };

    let input2 = seq![0x7Bu8, 0x00u8, 0x7Du8, 0x7Bu8, 0x00u8, 0x7Du8];

    nested_braces.lemma_parse_safe(input);
    nested_braces.lemma_parse_sound_value(input);
    nested_braces.lemma_parse_sound_consumption(input);
    nested_braces.lemma_parse_non_malleable(input, input2);
    let (n, v) = nested_braces.spec_parse(input)->0;
    nested_braces.lemma_serialize_len(v);

    let serialized = nested_braces.spec_serialize(v);
    nested_braces.nonmal_leaf_inv();
    assert(nested_braces.unambiguous());
    nested_braces.lemma_no_lookahead(input, input2);
    nested_braces.theorem_serialize_parse_roundtrip(v);
    nested_braces.theorem_parse_serialize_roundtrip(input);
}

} // verus!
#[test]
fn nested_braces_exec_parse() {
    let parser = Fix::<10, _>(NestedBracesBody);
    let input: &[u8] = &[0x7b, 0x7b, 0x00, 0x7d, 0x7d];
    let result = parser.parse(&input);

    println!("input buf: {:?}, parse result: {:?}", input, result);

    let parsed_value = match result {
        Ok((5, value @ NestedBracesT::Brace(_))) => {
            let NestedBracesT::Brace(inner) = &value else {
                unreachable!();
            };
            assert!(
                matches!(inner.as_ref(), NestedBracesT::Brace(inner2) if matches!(inner2.as_ref(), NestedBracesT::Eps))
            );
            value
        }
        other => panic!("unexpected parse result: {:?}", other),
    };

    let parsed_ref = &parsed_value;
    let mut serialized = Vec::<u8>::new();
    parser.ex_serialize(&parsed_ref, &mut serialized);
    println!(
        "serialized value: {:?}, output buf: {:?}",
        parsed_value, serialized
    );
    assert_eq!(serialized.as_slice(), input);

    let serialized_input = serialized.as_slice();
    let serialized_parse_result = parser.parse(&serialized_input);
    println!(
        "serialized input buf: {:?}, parse result: {:?}",
        serialized_input, serialized_parse_result
    );

    // Test with recursion limit exceeded
    let bad_input: &[u8] = &[
        0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x00, 0x7d, 0x7d, 0x7d,
        0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d,
    ];
    let bad_result = parser.parse(&bad_input);

    println!(
        "bad input buf: {:?}, parse result: {:?}",
        bad_input, bad_result
    );

    match &bad_result {
        Err(err) => {
            println!("bad parse error message: {}", err);
            assert_eq!(
                err.kind,
                crate::core::exec::ParseErrorKind::RecursionLimitExceeded
            );
        }
        other => panic!("expected recursion limit error, got {:?}", other),
    }
}
