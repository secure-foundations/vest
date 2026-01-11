use crate::combinators::*;
use crate::core::proof::*;
use crate::core::spec::*;
use vstd::prelude::*;

verus! {

pub enum NestedBracesT {
    Brace(Box<NestedBracesT>),
    Eps,
}

spec fn p_nested_braces(input: Seq<u8>) -> Option<(int, NestedBracesT)>
    decreases input.len(),
{
    let parse_fn = |rem: Seq<u8>|
        {
            if rem.len() < input.len() {
                p_nested_braces(rem)
            } else {
                None
            }
        };
    Mapped {
        inner: Choice(
            Terminated(
                Preceded(Tag { inner: U8, tag: 0x7Bu8 }, parse_fn),
                Tag { inner: U8, tag: 0x7Du8 },
            ),
            Tag { inner: U8, tag: 0x00u8 },
        ),
        mapper: |r|
            {
                match r {
                    Either::Left(inner) => NestedBracesT::Brace(Box::new(inner)),
                    Either::Right(_) => NestedBracesT::Eps,
                }
            },
    }.spec_parse(input)
}

} // verus!
