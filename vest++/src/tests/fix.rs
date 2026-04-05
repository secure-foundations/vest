use crate::combinators::mapped::spec::{LosslessMapper, LossyMapper, Mapper};
use crate::combinators::recursive::*;
use crate::combinators::*;
use crate::core::proof::*;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

/*
* Example recursive parser: nested braces
*/
/// Example recursive value type: nested braces `{...}` or empty `\0`.
pub enum NestedBracesT {
    /// A brace-wrapped recursive value: `'{' inner '}'`.
    Brace(Box<NestedBracesT>),
    /// The empty (base case) value: `'\0'`.
    Eps,
}

/// Mapper between `Sum<NestedBracesT, u8>` and `NestedBracesT`.
pub struct NestedBracesMapper;

impl Mapper for NestedBracesMapper {
    type In = Sum<NestedBracesT, u8>;

    type Out = NestedBracesT;

    open spec fn wf_in(&self, i: Self::In) -> bool {
        match i {
            Sum::Inl(_) => true,
            Sum::Inr(tag) => tag == 0x00u8,
        }
    }

    open spec fn spec_map(&self, i: Self::In) -> Self::Out {
        match i {
            Sum::Inl(inner) => NestedBracesT::Brace(Box::new(inner)),
            Sum::Inr(_) => NestedBracesT::Eps,
        }
    }

    open spec fn spec_map_rev(&self, o: Self::Out) -> Self::In {
        match o {
            NestedBracesT::Brace(inner) => Sum::Inl(*inner),
            NestedBracesT::Eps => Sum::Inr(0x00u8),
        }
    }
}

impl LossyMapper for NestedBracesMapper {
    proof fn lemma_sound_mapper(&self, o: Self::Out) {
        match o {
            NestedBracesT::Brace(_) => {},
            NestedBracesT::Eps => {},
        }
    }
}

impl LosslessMapper for NestedBracesMapper {
    proof fn lemma_lossless_mapper(&self, i: Self::In) {
        match i {
            Sum::Inl(_) => {},
            Sum::Inr(tag) => {
                assert(tag == 0x00u8);
            },
        }
    }

    proof fn lemma_mapper_wf_in_out(&self, i: Self::In) {
    }
}

/// One level of the nested-braces format: `'{' rec '}' | '\0'`.
pub open spec fn nested_braces_body<Rec>(rec: Rec) -> NestedBracesBodyComb<Rec> {
    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U8, tag: 0x7Bu8 }, rec),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: NestedBracesMapper,
    }
}

type NestedBracesBodyComb<Rec> = Mapped<
    Choice<Terminated<Preceded<Tag<U8, u8>, Rec>, Tag<U8, u8>>, Tag<U8, u8>>,
    NestedBracesMapper,
>;

/// [`SpecRecBody`] for the nested-braces example.
pub struct NestedBracesBody;

impl SpecRecBody for NestedBracesBody {
    type T = NestedBracesT;

    type Body = NestedBracesBodyComb<BundledSpecs<Self::T>>;

    open spec fn spec_body(&self, rec: BundledSpecs<Self::T>) -> Self::Body {
        nested_braces_body(rec)
    }
}

impl StrictRecBody for NestedBracesBody {
    proof fn lemma_body_all_inv_preservation(&self, rec: BundledSpecs<Self::T>) {
    }
}

/// TODO: hide/automate this?
proof fn nested_braces_unambiguous_gas(gas: nat)
    ensures
        Fix::<10, NestedBracesBody>(NestedBracesBody).unambiguity_gas(gas),
    decreases gas,
{
    if gas > 0 {
        nested_braces_unambiguous_gas((gas - 1) as nat);
    }
}

proof fn nested_braces_sound_parser() {
    let nested_braces = Fix::<10, _>(NestedBracesBody);

    let input = seq![0x7Bu8, 0x00u8, 0x7Du8];

    assert(nested_braces.spec_parse(input) == Some(
        (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
    )) by {
        let cb = nested_braces.specs_callback(10);
        let body10 = nested_braces_body(cb);
        assert(body10.spec_parse(input) == Some(
            (3int, NestedBracesT::Brace(Box::new(NestedBracesT::Eps))),
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
    nested_braces_unambiguous_gas(10);
    assert(nested_braces.unambiguous());
    nested_braces.lemma_no_lookahead(input, input2);
    nested_braces.theorem_serialize_parse_roundtrip(v);
    nested_braces.theorem_parse_serialize_roundtrip(input);
}

} // verus!
