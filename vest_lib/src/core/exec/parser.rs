//! Executable parser traits.
use crate::core::proof::Productive;
use crate::core::spec::{SafeParser, SpecParser};
use vstd::prelude::*;

use super::ParseError;

verus! {

/// Result returned by an executable parser.
///
/// On success, the `usize` is the number of input bytes consumed and `O` is the
/// parsed value. A parser may leave a suffix of its input unconsumed.
pub type PResult<O> = Result<(usize, O), ParseError>;

/// Relates an executable parse result to its pure [`SpecParser`] result.
pub open spec fn parse_matches_spec<O: DeepView>(
    r: PResult<O>,
    spec_parse: Option<(int, O::V)>,
) -> bool {
    &&& r is Ok <==> spec_parse is Some
    &&& r is Err <==> spec_parse is None
    &&& r matches Ok((n, v)) ==> spec_parse == Some((n as int, v.deep_view()))
}

/// An executable parser proved equivalent to a pure [`SpecParser`].
///
/// `Input` is normally `&[u8]`. Successful parsing returns both the consumed
/// byte count and a value whose deep view is exactly the value returned by
/// `SpecParser::spec_parse`.
pub trait Parser<Input: View<V = Seq<u8>>>: SpecParser {
    /// Executable value returned by this parser.
    type PT: DeepView<V = Self::PVal>;

    /// Extra invariant required by this parser's executable implementation.
    ///
    /// Most formats leave this as `true`; functional and recursive
    /// parser callbacks use it to connect executable code to their specifications.
    open spec fn exec_inv(&self) -> bool {
        true
    }

    /// Parses a prefix of `ibuf`.
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

impl<Spec, Exec> Productive for (Spec, Exec) where Spec: Productive {
    open spec fn productive_inv(&self) -> bool {
        self.0.productive_inv()
    }

    proof fn lemma_productive(&self, input: Seq<u8>) {
        self.0.lemma_productive(input);
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

impl<P: Productive> Productive for &P {
    open spec fn productive_inv(&self) -> bool {
        (*self).productive_inv()
    }

    proof fn lemma_productive(&self, s: Seq<u8>) {
        (*self).lemma_productive(s);
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

pub proof fn lemma_ref_safe_productive_inv<P>(parser: &P) where P: Productive
    requires
        parser.safe_inv(),
        parser.productive_inv(),
    ensures
        <&P as SafeParser>::safe_inv(&parser),
        <&P as Productive>::productive_inv(&parser),
{
}

} // verus!
