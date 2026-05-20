//! Executable parser traits.
use crate::core::spec::{SafeParser, SpecParser};
use vstd::prelude::*;

use super::ParseError;

verus! {

pub type PResult<O> = Result<(usize, O), ParseError>;

pub open spec fn parse_matches_spec<O: DeepView>(
    r: PResult<O>,
    spec_parse: Option<(int, O::V)>,
) -> bool {
    &&& r is Ok <==> spec_parse is Some
    &&& r is Err <==> spec_parse is None
    &&& r matches Ok((n, v)) ==> spec_parse == Some((n as int, v.deep_view()))
}

pub trait Parser<Input: View<V = Seq<u8>>>: SpecParser {
    type PT: DeepView<V = Self::PVal>;

    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn parse(&self, ibuf: &Input) -> (r: PResult<Self::PT>)
        requires
            self.exec_inv(),
        ensures
            parse_matches_spec(r, self.spec_parse(ibuf@)),
    ;
}

impl<Spec, Exec> SpecParser for (Spec, Exec) where Spec: SpecParser {
    type PVal = Spec::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.0.spec_parse(ibuf)
    }
}

impl<Spec, Exec> SafeParser for (Spec, Exec) where Spec: SafeParser {
    open spec fn safe_inv(&self) -> bool {
        self.0.safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        self.0.lemma_parse_safe(ibuf);
    }
}

impl<I, T, Spec, Exec> Parser<I> for (Spec, Exec) where
    I: View<V = Seq<u8>>,
    T: DeepView<V = Spec::PVal>,
    Spec: SpecParser,
    Exec: Fn(&I) -> PResult<T>,
 {
    type PT = T;

    open spec fn exec_inv(&self) -> bool {
        &&& forall|i: &I| call_requires(self.1, (i,))
        &&& forall|i: &I, r: PResult<T>|
            #![auto]
            call_ensures(self.1, (i,), r) ==> parse_matches_spec(r, self.spec_parse(i@))
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<T>) {
        (self.1)(ibuf)
    }
}

impl<P: SpecParser> SpecParser for &P {
    type PVal = P::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        (*self).spec_parse(ibuf)
    }
}

impl<P: SafeParser> SafeParser for &P {
    open spec fn safe_inv(&self) -> bool {
        (*self).safe_inv()
    }

    proof fn lemma_parse_safe(&self, ibuf: Seq<u8>) {
        (*self).lemma_parse_safe(ibuf);
    }
}

impl<I, P> Parser<I> for &P where I: View<V = Seq<u8>>, P: Parser<I> {
    type PT = P::PT;

    open spec fn exec_inv(&self) -> bool {
        (*self).exec_inv()
    }

    fn parse(&self, ibuf: &I) -> (r: PResult<Self::PT>) {
        (*self).parse(ibuf)
    }
}

// pub trait Parser: SpecParser {
//     type Ty<'i>: DeepView<V = Self::PVal>;
//     fn parse<'i, I: InputBuf>(&self, ibuf: &'i I) -> (r: Result<(usize, Self::Ty<'i>), ParseError>)
//         ensures
//             r is Ok <==> self.spec_parse(ibuf@) is Some,
//             r is Err <==> self.spec_parse(ibuf@) is None,
//             r matches Ok((n, v)) ==> self.spec_parse(ibuf@) == Some((n as int, v.deep_view())),
//     ;
// }
// impl<Input, Ty, Spec, Exec> SpecParser for (Spec, Exec) where
//     Spec: SpecParser,
//     Exec: Fn(Input) -> Result<(usize, Ty), ParseError>,
//  {
//     type PVal = Spec::PVal;
//     open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
//         let (spec, exec) = self;
//         spec.spec_parse(ibuf)
//     }
// }
// impl<Input, Ty, Spec, Exec> Parser for (Spec, Exec) where
//     Spec: SpecParser,
//     Exec: Fn(Input) -> Result<(usize, Ty), ParseError>,
//     Ty: DeepView<V = Spec::PVal>,
//  {
//     type Ty<'i> = Ty;
//     fn parse<'i, I: InputBuf>(&self, ibuf: &'i I) -> (r: Result<(usize, Self::Ty<'i>), ParseError>)
//         ensures
//             r is Ok <==> self.spec_parse(ibuf@) is Some,
//             r is Err <==> self.spec_parse(ibuf@) is None,
//             r matches Ok((n, v)) ==> self.spec_parse(ibuf@) == Some((n as int, v.deep_view())),
//     {
//         let (spec, exec) = self;
//         exec(ibuf)
//     }
// }
// type ParserFnWithSpec<Input, Ty, Spec, Exec> where
//     Spec: SpecParser,
//     Exec: Fn(Input) -> Result<(usize, Ty), ParseError>,
//  = (Spec, Exec);
// pub trait VerifiedParser where
//     Self: Parser + SpecParser,
//     for <'i>Self::Ty<'i>: DeepView<V = Self::PVal>,
//  {
//      proof fn exec_spec_equiv<'i, I: InputBuf>(&self, ibuf: &'i I) -> (r: Result<(usize, Self::Ty<'i>), ParseError>)
//         ensures
//             r is Ok <==> self.spec_parse(ibuf@) is Some,
//             r is Err <==> self.spec_parse(ibuf@) is None,
//             r matches Ok((n, v)) ==> self.spec_parse(ibuf@) == Some((n as int, v.deep_view())),
//     ;
// }
// pub trait Validator {
//     type Err;
//     fn validate<'i, I: InputBuf>(&self, ibuf: &'i I) -> Result<usize, ParseError<Self::Err>>;
// }
// pub trait Deserializer {
//     type Ty<'i>: DeepView;
//     fn deserialize<'i, I: InputBuf>(&self, ibuf: &'i I) -> Self::Ty<'i>;
// }
} // verus!
