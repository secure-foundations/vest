use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that sequentially applies two combinators and returns the result of the first one.
pub struct Terminated<Fst, Snd>(pub Fst, pub Snd);

impl<Fst: View, Snd: View> View for Terminated<Fst, Snd> {
    type V = Terminated<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        Terminated(self.0@, self.1@)
    }
}

impl<Fst: SecureSpecCombinator, Snd: SpecCombinator<Result = ()>> SpecCombinator for Terminated<
    Fst,
    Snd,
> {
    type Result = Fst::Result;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        if let Ok((n, (v, ()))) = (self.0, self.1).spec_parse(s) {
            Ok((n, v))
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, (v, ()))) = (self.0, self.1).spec_parse(s) {
            (self.0, self.1).spec_parse_wf(s);
        }
    }

    open spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        (self.0, self.1).spec_serialize((v, ()))
    }
}

impl<
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator<Result = ()>,
> SecureSpecCombinator for Terminated<Fst, Snd> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        (self.0, self.1).theorem_serialize_parse_roundtrip((v, ()));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, (v, ()))) = (self.0, self.1).spec_parse(buf) {
            (self.0, self.1).theorem_parse_serialize_roundtrip(buf);
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            (self.0, self.1).lemma_prefix_secure(s1, s2);
        }
    }
}

impl<I, O, Fst, Snd> Combinator<I, O> for Terminated<Fst, Snd> where
    I: VestSecretInput,
    O: VestSecretOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O, Result = ()>,
    Fst::V: SecureSpecCombinator<Result = <Fst::Result as View>::V>,
    Snd::V: SecureSpecCombinator<Result = ()>,
 {
    type Result = Fst::Result;

    open spec fn spec_length(&self) -> Option<usize> {
        (self.0, self.1).spec_length()
    }

    fn length(&self) -> Option<usize> {
        (&self.0, &self.1).length()
    }

    open spec fn parse_requires(&self) -> bool {
        (&self.0, &self.1).parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Result), ParseError> {
        let (n, (v, ())) = (&self.0, &self.1).parse(s.clone())?;
        Ok((n, v))
    }

    open spec fn serialize_requires(&self) -> bool {
        (&self.0, &self.1).serialize_requires()
    }

    fn serialize<'b>(&self, v: Self::Result, data: &'b mut O, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        (&self.0, &self.1).serialize((v, ()), data, pos)
    }
}

} // verus!
