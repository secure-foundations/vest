//! Executable parser traits.
use crate::core::spec::SpecParser;
use vstd::prelude::*;

use super::ParseError;

verus! {

pub type PResult<T> = Result<(usize, T), ParseError>;

pub trait Parser<Input: View<V = Seq<u8>>, Ty: DeepView<V = Self::PVal>>: SpecParser {
    open spec fn exec_inv(&self) -> bool {
        true
    }

    fn parse(&self, ibuf: Input) -> (r: PResult<Ty>)
        requires
            self.exec_inv(),
        ensures
            r is Ok <==> self.spec_parse(ibuf@) is Some,
            r is Err <==> self.spec_parse(ibuf@) is None,
            r matches Ok((n, v)) ==> self.spec_parse(ibuf@) == Some((n as int, v.deep_view())),
    ;

    /// This is intended for DSL-generated entry points around user-defined formats.
    fn parse_with_format(&self, current_format: &'static str, ibuf: Input) -> (r: PResult<Ty>)
        requires
            self.exec_inv(),
        ensures
            r is Ok <==> self.spec_parse(ibuf@) is Some,
            r is Err <==> self.spec_parse(ibuf@) is None,
            r matches Ok((n, v)) ==> self.spec_parse(ibuf@) == Some((n as int, v.deep_view())),
    {
        match self.parse(ibuf) {
            Ok((n, v)) => Ok((n, v)),
            Err(err) => Err(err.push_format(current_format)),
        }
    }
}

impl<Spec, Exec> SpecParser for (Spec, Exec) where Spec: SpecParser {
    type PVal = Spec::PVal;

    open spec fn spec_parse(&self, ibuf: Seq<u8>) -> Option<(int, Self::PVal)> {
        self.0.spec_parse(ibuf)
    }
}

impl<Input, Ty, Spec, Exec> Parser<Input, Ty> for (Spec, Exec) where
    Input: View<V = Seq<u8>>,
    Ty: DeepView<V = Spec::PVal>,
    Spec: SpecParser,
    Exec: Fn(Input) -> PResult<Ty>,
 {
    open spec fn exec_inv(&self) -> bool {
        &&& forall|i: Input| call_requires(self.1, (i,))
        &&& forall|i: Input, r: PResult<Ty>|
            call_ensures(self.1, (i,), r) ==> {
                &&& r is Ok <==> self.spec_parse(i@) is Some
                &&& r is Err <==> self.spec_parse(i@) is None
                &&& r matches Ok((n, v)) ==> self.spec_parse(i@) == Some((n as int, v.deep_view()))
            }
    }

    fn parse(&self, ibuf: Input) -> (r: PResult<Ty>) {
        (self.1)(ibuf)
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
