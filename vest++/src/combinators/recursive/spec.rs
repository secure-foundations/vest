use crate::core::{proof::*, spec::*};
use vstd::prelude::*;

verus! {

pub open spec fn good_parser_fn<T: SpecType>(parser_fn: ParserSpecFn<T>) -> bool {
    forall|i: Seq<u8>| #[trigger]
        parser_fn(i) matches Some((n, v)) ==> 0 <= n <= i.len() && (parser_fn).wf(v)
}

// pub trait PBody {
//     type T;
//     spec fn body(&self, rec: ParserSpecFn<Self::T>) -> ParserSpecFn<Self::T>;
//     proof fn good_body(&self)
//         ensures
//             forall|rec: ParserSpecFn<Self::T>|
// }
} // verus!
