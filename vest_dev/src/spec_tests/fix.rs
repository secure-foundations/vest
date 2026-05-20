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
use crate::core::exec::ParseError;
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
    type Input = Sum<NestedBracesTSpec, u8>;

    type Output = NestedBracesTSpec;

    open spec fn spec_map(&self, i: Self::Input) -> Self::Output {
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
    type Input = NestedBracesTSpec;

    type Output = Sum<NestedBracesTSpec, u8>;

    open spec fn spec_map(&self, o: Self::Input) -> Self::Output {
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
            NestedBracesT::Brace(inner) => Sum::Inl(inner),
            NestedBracesT::Eps => Sum::Inr(0x00u8),
        }
    }
}

/// One level of the nested-braces format: `'{' rec '}' | '\0'`.
// pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec>
pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec> {
    Mapped {
        inner: Choice(WithSuffixTag(U8, 0x7Du8, WithPrefixTag(U8, 0x7Bu8, rec)), Const(U8, 0x00u8)),
        mapper: BiMap(NestedBracesMap, NestedBracesMapRev),
    }
}

type NestedBracesBodyComb<Rec> = Mapped<
    Choice<WithSuffixTag<U8, WithPrefixTag<U8, Rec>>, Const<U8, u8>>,
    BiMap<NestedBracesMap, NestedBracesMapRev>,
>;

/// [`SpecRecBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl SpecRecBody for NestedBracesBody {
    type Param = ();

    type T = NestedBracesTSpec;

    type Body = NestedBracesBodyComb<BundledSpecs<Self::T>>;

    open spec fn spec_body(_param: (), rec: ParamRecSpecs<Self::Param, Self::T>) -> Self::Body {
        nested_braces_body(rec(()))
    }
}

impl<'i> ParserRecBody<&'i [u8]> for NestedBracesBody {
    type EP = ();

    type O = NestedBracesT;

    fn parse_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&(), &&'i [u8]) -> PResult<Self::O> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;

        let _total_len = ibuf.len();
        let (n1, first) = U8.parse(ibuf)?;
        match first {
            0x00u8 => {
                let value = NestedBracesT::Eps;
                Ok((n1, value))
            },
            0x7Bu8 => {
                let rest = ibuf.skip(n1);
                let (n2, inner) = exec_rec(&(), &rest)?;
                let rest2 = rest.skip(n2);
                let (n3, _) = Const(U8, 0x7Du8).parse(&rest2)?;
                let total = n1 + n2 + n3;
                let value = NestedBracesT::Brace(Box::new(inner));
                Ok((total, value))
            },
            _ => { Err(ParseError::invalid_tag()) },
        }
    }
}

impl<'s> SerializerRecBody<&'s NestedBracesT> for NestedBracesBody {
    type EP = ();

    fn serialize_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &'s NestedBracesT,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&(), &'s NestedBracesT, &mut Vec<u8>) {
        match v {
            NestedBracesT::Eps => {
                U8.ex_serialize(0x00u8, obuf);
            },
            NestedBracesT::Brace(inner) => {
                U8.ex_serialize(0x7Bu8, obuf);
                exec_rec(&(), inner, obuf);
                U8.ex_serialize(0x7Du8, obuf);
            },
        }
    }
}

impl<'s> PrepareRecBody<&'s NestedBracesT> for NestedBracesBody {
    type EP = ();

    fn prepare_body<Exec>(
        &self,
        _param: &(),
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &'s NestedBracesT,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&(), &'s NestedBracesT) -> Result<usize, PreSerializeError>,
     {
        match v {
            NestedBracesT::Eps => U8.prepare(0x00u8),
            NestedBracesT::Brace(inner) => {
                let l1 = U8.prepare(0x7Bu8)?;
                let l2 = exec_rec(&(), inner)?;
                let l3 = U8.prepare(0x7Du8)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
                let sum2 = sum1.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?;
                Ok(sum2)
            },
        }
    }
}

impl StrictRecBody for NestedBracesBody {
    proof fn lemma_body_all_inv_preservation(_param: (), rec: ParamRecSpecs<Self::Param, Self::T>) {
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = FixWith::<10, _, _>(NestedBracesBody, ());

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesTSpec::Brace(Box::new(NestedBracesTSpec::Eps))),
    )) by {
        let cb = FixWith::<10, NestedBracesBody, ()>::specs_callback(10);
        let body10 = nested_braces_body(cb(()));
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

/*
* Example parameterized recursive parser: tag-threaded chain
*/

#[derive(Debug, DeepView)]
pub enum TaggedChainT {
    End,
    Step(u8, Box<TaggedChainT>),
}

pub struct TaggedChainMap;

pub struct TaggedChainMapRev;

impl SpecMap for TaggedChainMap {
    type Input = Sum<(u8, TaggedChainTSpec), u8>;

    type Output = TaggedChainTSpec;

    open spec fn spec_map(&self, i: Self::Input) -> Self::Output {
        match i {
            Sum::Inl((next_tag, tail)) => TaggedChainTSpec::Step(next_tag, Box::new(tail)),
            Sum::Inr(_) => TaggedChainTSpec::End,
        }
    }
}

impl fns::Map<Sum<(u8, TaggedChainT), u8>> for TaggedChainMap {
    type O = TaggedChainT;

    fn map(&self, i: Sum<(u8, TaggedChainT), u8>) -> Self::O {
        match i {
            Sum::Inl((next_tag, tail)) => TaggedChainT::Step(next_tag, Box::new(tail)),
            Sum::Inr(_) => TaggedChainT::End,
        }
    }
}

impl SpecMap for TaggedChainMapRev {
    type Input = TaggedChainTSpec;

    type Output = Sum<(u8, TaggedChainTSpec), u8>;

    open spec fn spec_map(&self, o: Self::Input) -> Self::Output {
        match o {
            TaggedChainTSpec::Step(next_tag, tail) => Sum::Inl((next_tag, *tail)),
            TaggedChainTSpec::End => Sum::Inr(0x00u8),
        }
    }
}

impl<'s> fns::Map<&'s TaggedChainT> for TaggedChainMapRev {
    type O = Sum<(u8, &'s TaggedChainT), u8>;

    fn map(&self, o: &'s TaggedChainT) -> Self::O {
        match o {
            TaggedChainT::Step(next_tag, tail) => Sum::Inl((*next_tag, &**tail)),
            TaggedChainT::End => Sum::Inr(0x00u8),
        }
    }
}

type TaggedChainBodyComb<Rec> = Mapped<
    Choice<Cond<WithPrefixTag<U8, Bind<U8, Rec>>>, Cond<Const<U8, u8>>>,
    BiMap<TaggedChainMap, TaggedChainMapRev>,
>;

pub struct TaggedChainBody;

impl SpecRecBody for TaggedChainBody {
    type Param = u8;

    type T = TaggedChainTSpec;

    type Body = TaggedChainBodyComb<ParamRecSpecs<Self::Param, Self::T>>;

    open spec fn spec_body(
        current_tag: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) -> Self::Body {
        Mapped {
            inner: Choice(
                Cond(
                    current_tag != 0u8,
                    WithPrefixTag(U8, current_tag, Bind(U8, |next_tag: u8| rec(next_tag))),
                ),
                Cond(current_tag == 0u8, Const(U8, 0x00u8)),
            ),
            mapper: BiMap(TaggedChainMap, TaggedChainMapRev),
        }
    }
}

impl<'i> ParserRecBody<&'i [u8]> for TaggedChainBody {
    type EP = u8;

    type O = TaggedChainT;

    fn parse_body<Exec>(
        &self,
        current_tag: &u8,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        ibuf: &&'i [u8],
    ) -> PResult<Self::O> where Exec: Fn(&u8, &&'i [u8]) -> PResult<Self::O> {
        broadcast use crate::core::spec::SafeParser::lemma_parse_safe;
        broadcast use vstd::seq_lib::lemma_seq_skip_of_skip;

        let _total_len = ibuf.len();

        match *current_tag {
            0u8 => {
                let (n1, _) = Const(U8, 0x00u8).parse(ibuf)?;
                let value = TaggedChainT::End;
                Ok((n1, value))
            },
            _ => {
                let (n1, _) = Const(U8, *current_tag).parse(ibuf)?;
                let rest = ibuf.skip(n1);
                let (n2, next_tag) = U8.parse(&rest)?;
                let rest2 = rest.skip(n2);
                let (n3, tail) = exec_rec(&next_tag, &rest2)?;
                let total = n1 + n2 + n3;
                let value = TaggedChainT::Step(next_tag, Box::new(tail));
                Ok((total, value))
            },
        }
    }
}

impl<'s> SerializerRecBody<&'s TaggedChainT> for TaggedChainBody {
    type EP = u8;

    fn serialize_body<Exec>(
        &self,
        current_tag: &u8,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &'s TaggedChainT,
        obuf: &mut Vec<u8>,
    ) where Exec: Fn(&u8, &'s TaggedChainT, &mut Vec<u8>) {
        match v {
            TaggedChainT::End => {
                U8.ex_serialize(0x00u8, obuf);
            },
            TaggedChainT::Step(next_tag, tail) => {
                U8.ex_serialize(*current_tag, obuf);
                U8.ex_serialize(*next_tag, obuf);
                exec_rec(next_tag, tail, obuf);
            },
        }
    }
}

impl<'s> PrepareRecBody<&'s TaggedChainT> for TaggedChainBody {
    type EP = u8;

    fn prepare_body<Exec>(
        &self,
        current_tag: &u8,
        Ghost(spec_rec): Ghost<ParamRecSpecs<Self::Param, Self::T>>,
        exec_rec: Exec,
        v: &'s TaggedChainT,
    ) -> Result<usize, PreSerializeError> where
        Exec: Fn(&u8, &'s TaggedChainT) -> Result<usize, PreSerializeError>,
     {
        match v {
            TaggedChainT::End => {
                if *current_tag == 0u8 {
                    U8.prepare(0x00u8)
                } else {
                    Err(PreSerializeError::NotCompliant(ComplianceErrorKind::CondRejected))
                }
            },
            TaggedChainT::Step(next_tag, tail) => {
                if *current_tag == 0u8 {
                    return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::CondRejected));
                }
                let l1 = U8.prepare(*current_tag)?;
                let l2 = U8.prepare(*next_tag)?;
                let l3 = exec_rec(next_tag, tail)?;
                let sum1 = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?;
                let sum2 = sum1.checked_add(l3).ok_or(PreSerializeError::LengthTooLarge)?;
                Ok(sum2)
            },
        }
    }
}

impl StrictRecBody for TaggedChainBody {
    proof fn lemma_body_all_inv_preservation(
        _param: Self::Param,
        rec: ParamRecSpecs<Self::Param, Self::T>,
    ) {
    }
}

proof fn tagged_chain_sound_parser() {
    let tagged_chain = FixWith::<10, _, _>(TaggedChainBody, 0x7Au8);

    let input = seq![0x7Au8, 0x5Au8, 0x5Au8, 0x33u8, 0x33u8, 0x00u8, 0x00u8];
    let value = TaggedChainTSpec::Step(
        0x5Au8,
        Box::new(
            TaggedChainTSpec::Step(
                0x33u8,
                Box::new(TaggedChainTSpec::Step(0x00u8, Box::new(TaggedChainTSpec::End))),
            ),
        ),
    );

    tagged_chain.lemma_parse_safe(input);
    tagged_chain.lemma_parse_sound_value(input);
    tagged_chain.lemma_parse_sound_consumption(input);
    tagged_chain.lemma_serialize_len(value);
    tagged_chain.theorem_parse_serialize_roundtrip(input);
}

} // verus!
#[test]
fn nested_braces_exec_parse() {
    fn nested_braces(depth: usize) -> NestedBracesT {
        let mut value = NestedBracesT::Eps;
        for _ in 0..depth {
            value = NestedBracesT::Brace(Box::new(value));
        }
        value
    }

    let fmt = FixWith::<10, _, _>(NestedBracesBody, ());
    let input: &[u8] = &[0x7b, 0x7b, 0x00, 0x7d, 0x7d];
    let result = fmt.parse(&input);

    println!("input buf: {:X?}, parse result: {:?}", input, result);

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
    let prepared = fmt.prepare(parsed_ref);
    assert!(matches!(prepared, Ok(len) if len == input.len()));

    let len = prepared.unwrap();
    let mut serialized = Vec::with_capacity(len);
    fmt.serialize(&parsed_ref, &mut serialized);
    println!(
        "serialized value: {:?}, output buf: {:X?}",
        parsed_value, serialized
    );
    assert_eq!(serialized.as_slice(), input);

    let serialized_input = serialized.as_slice();
    let serialized_parse_result = fmt.parse(&serialized_input);
    println!(
        "serialized input buf: {:X?}, parse result: {:?}",
        serialized_input, serialized_parse_result
    );

    // Test with recursion limit exceeded
    let bad_input: &[u8] = &[
        0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x7b, 0x00, 0x7d, 0x7d, 0x7d,
        0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d, 0x7d,
    ];
    let bad_result = fmt.parse(&bad_input);

    println!(
        "bad input buf: {:X?}, parse result: {:?}",
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

    let too_deep = nested_braces(11);
    let too_deep_prepared = fmt.prepare(&too_deep);
    println!("too-deep nested prepare result: {:?}", too_deep_prepared);
    assert!(matches!(
        too_deep_prepared,
        Err(PreSerializeError::NotCompliant(
            ComplianceErrorKind::RecursionLimitExceeded
        ))
    ));
}

#[test]
fn tagged_chain_exec_parse_serialize() {
    let fmt = FixWith::<10, _, _>(TaggedChainBody, 0x7Au8);
    let input: &[u8] = &[0x7A, 0x5A, 0x5A, 0x33, 0x33, 0x00, 0x00];
    let result = fmt.parse(&input);

    println!(
        "tagged-chain input buf: {:X?}, parse result: {:?}",
        input, result
    );

    let parsed_value = match result {
        Ok((7, TaggedChainT::Step(0x5A, tail1))) => {
            assert!(matches!(
                tail1.as_ref(),
                TaggedChainT::Step(0x33, tail2)
                    if matches!(tail2.as_ref(), TaggedChainT::Step(0x00, tail3)
                        if matches!(tail3.as_ref(), TaggedChainT::End))
            ));
            TaggedChainT::Step(0x5A, tail1)
        }
        other => panic!("unexpected tagged-chain parse result: {:?}", other),
    };

    let prepared = fmt.prepare(&parsed_value);
    assert!(matches!(prepared, Ok(len) if len == input.len()));
    let len = prepared.unwrap();
    let mut serialized = Vec::with_capacity(len);
    fmt.serialize(&parsed_value, &mut serialized);
    println!(
        "tagged-chain parsed value: {:?}, serialized buf: {:X?}",
        parsed_value, serialized
    );
    assert_eq!(serialized.as_slice(), input);
}
