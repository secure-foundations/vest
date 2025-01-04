use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that checks if `cond` is true and then delegates to the `inner` combinator.
pub struct Cond<Inner> {
    /// The condition to check before parsing or serializing.
    pub cond: bool,
    /// The combinator to delegate to if `cond` is true.
    pub inner: Inner,
}

impl<Inner: View> View for Cond<Inner> {
    type V = Cond<Inner::V>;

    open spec fn view(&self) -> Self::V {
        Cond { cond: self.cond, inner: self.inner@ }
    }
}

impl<Inner: SpecCombinator> SpecCombinator for Cond<Inner> {
    type Result = Inner::Result;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Result), ()> {
        if self.cond {
            self.inner.spec_parse(s)
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if self.cond {
            self.inner.spec_parse_wf(s);
        }
    }

    open spec fn spec_serialize(&self, v: Self::Result) -> Result<Seq<u8>, ()> {
        if self.cond {
            self.inner.spec_serialize(v)
        } else {
            Err(())
        }
    }
}

impl<Inner: SecureSpecCombinator> SecureSpecCombinator for Cond<Inner> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Result) {
        if self.cond {
            self.inner.theorem_serialize_parse_roundtrip(v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if self.cond {
            self.inner.theorem_parse_serialize_roundtrip(buf);
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Inner::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.cond {
            self.inner.lemma_prefix_secure(s1, s2);
        }
    }
}

impl<I: VestSecretInput, O: VestSecretOutput<I>, Inner: Combinator<I, O>> Combinator<I, O> for Cond<
    Inner,
> where Inner::V: SecureSpecCombinator<Result = <Inner::Result as View>::V> {
    type Result = Inner::Result;

    open spec fn spec_length(&self) -> Option<usize> {
        if self.cond@ {
            self.inner.spec_length()
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if self.cond {
            self.inner.length()
        } else {
            None
        }
    }

    open spec fn parse_requires(&self) -> bool {
        self.inner.parse_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Result), ParseError> {
        if self.cond {
            self.inner.parse(s)
        } else {
            Err(ParseError::CondFailed)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.inner.serialize_requires()
    }

    fn serialize(&self, v: Self::Result, data: &mut O, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        if self.cond {
            self.inner.serialize(v, data, pos)
        } else {
            Err(SerializeError::CondFailed)
        }
    }
}

} // verus!
