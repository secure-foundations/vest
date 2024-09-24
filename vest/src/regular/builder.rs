use crate::properties::*;
use vstd::prelude::*;

verus! {

/// An abstraction over a suspended computation involving a sequence of bytes.
pub trait Builder {
    /// The value of the computation.
    spec fn value(&self) -> Seq<u8>;

    /// Ensures that the value of the computation is well-formed.
    proof fn value_wf(&self)
        ensures
            self.value().len() <= usize::MAX,
    ;

    /// The length of the bytes value.
    fn length(&self) -> (res: usize)
        ensures
            res == self.value().len(),
    ;

    /// Serializes the value of the computation into a mutable byte vector.
    fn into_mut_vec(&self, data: &mut Vec<u8>, pos: usize)
        requires
            0 <= pos + self.value().len() <= old(data)@.len() <= usize::MAX,
        ensures
            data@.len() == old(data)@.len(),
            seq_splice(old(data)@, pos, self.value()) == data@,
    ;

    /// Serializes the value of the computation into a byte vector.
    fn into_vec(&self) -> (res: Vec<u8>)
        ensures
            res@ == self.value(),
    {
        let mut res = init_vec_u8(self.length());
        self.into_mut_vec(&mut res, 0);
        assert(res@ == seq_splice(res@, 0, self.value()));
        assert(seq_splice(res@, 0, self.value()) == self.value());
        res
    }
}

/// Combinator that encapsulates a suspended computation for efficient serialization.
pub struct BuilderCombinator<T>(pub T);

impl<T> View for BuilderCombinator<T> {
    type V = BuilderCombinator<T>;

    open spec fn view(&self) -> Self::V {
        *self
    }
}

impl<T: Builder> SpecCombinator for BuilderCombinator<T> {
    type SpecResult = ();

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, ()), ()> {
        if s == self.0.value() {
            Ok((s.len() as usize, ()))
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
    }

    open spec fn spec_serialize(&self, v: ()) -> Result<Seq<u8>, ()> {
        Ok(self.0.value())
    }
}

impl<T: Builder> SecureSpecCombinator for BuilderCombinator<T> {
    open spec fn spec_is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: ()) {
        self.0.value_wf()
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.0.value_wf();
        assert(buf.subrange(0, buf.len() as int) == buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }
}

impl<T> Combinator for BuilderCombinator<T> where T: Builder + View, T::V: Builder {
    type Result<'a> = ();

    type Owned = ();

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        false
    }

    fn parse(&self, s: &[u8]) -> (res: Result<(usize, ()), ParseError>) {
        let v = self.0.into_vec();
        proof {
            self.0.value_wf();
        }
        if compare_slice(s, v.as_slice()) {
            Ok((s.len(), ()))
        } else {
            Err(ParseError::BuilderError)
        }
    }

    fn serialize(&self, v: (), data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        if self.0.length() <= data.len() && pos <= data.len() - self.0.length() {
            self.0.into_mut_vec(data, pos);
            assert(pos + self.0.value().len() <= data@.len());
            assert(data@ == seq_splice(old(data)@, pos, self.spec_serialize(()).unwrap()));
            assert(data@.subrange(pos as int, pos + self.0.value().len() as int) == self.0.value());
            Ok(self.0.length())
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
