use super::disjoint::{DisjointFrom, SpecDisjointFrom};
use crate::properties::*;
use vstd::prelude::*;

verus! {

#[allow(missing_docs)]
pub enum Either<A, B> {
    Left(A),
    Right(B),
}

impl<A: View, B: View> View for Either<A, B> {
    type V = Either<A::V, B::V>;

    open spec fn view(&self) -> Either<A::V, B::V> {
        match self {
            Either::Left(v) => Either::Left(v@),
            Either::Right(v) => Either::Right(v@),
        }
    }
}

/// Combinator that tries the `Fst` combinator and if it fails, tries the `Snd` combinator.
pub struct OrdChoice<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> OrdChoice<Fst, Snd> where
    Fst: Combinator,
    Snd: Combinator + DisjointFrom<Fst>,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V> + SpecDisjointFrom<Fst::V>,
 {
    /// Creates a new `OrdChoice` combinator.
    /// > **Note**: The `Snd` parser must be disjoint from the `Fst` parser.
    pub fn new(parser1: Fst, parser2: Snd) -> (o: Self)
        requires
            parser2@.spec_disjoint_from(&parser1@),
        ensures
            o.0 == parser1 && o.1 == parser2,
    {
        OrdChoice(parser1, parser2)
    }
}

impl<Fst, Snd> View for OrdChoice<Fst, Snd> where
    Fst: Combinator,
    Snd: Combinator + DisjointFrom<Fst>,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V> + SpecDisjointFrom<Fst::V>,
 {
    type V = OrdChoice<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        OrdChoice(self.0@, self.1@)
    }
}

impl<Fst, Snd> SpecCombinator for OrdChoice<Fst, Snd> where
    Fst: SpecCombinator,
    Snd: SpecCombinator + SpecDisjointFrom<Fst>,
 {
    type SpecResult = Either<Fst::SpecResult, Snd::SpecResult>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if self.1.spec_disjoint_from(&self.0) {
            if let Ok((n, v)) = self.0.spec_parse(s) {
                Ok((n, Either::Left(v)))
            } else {
                if let Ok((n, v)) = self.1.spec_parse(s) {
                    Ok((n, Either::Right(v)))
                } else {
                    Err(())
                }
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, v)) = self.0.spec_parse(s) {
            self.0.spec_parse_wf(s);
        } else {
            if let Ok((n, v)) = self.1.spec_parse(s) {
                self.1.spec_parse_wf(s);
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if self.1.spec_disjoint_from(&self.0) {
            match v {
                Either::Left(v) => self.0.spec_serialize(v),
                Either::Right(v) => self.1.spec_serialize(v),
            }
        } else {
            Err(())
        }
    }
}

impl<Fst, Snd> SecureSpecCombinator for OrdChoice<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator + SpecDisjointFrom<Fst>,
 {
    open spec fn spec_is_prefix_secure() -> bool {
        Fst::spec_is_prefix_secure() && Snd::spec_is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.1.spec_disjoint_from(&self.0) {
            // must also explicitly state that parser1 will fail on anything that parser2 will succeed on
            self.1.spec_parse_disjoint_on(&self.0, s1.add(s2));
            if Self::spec_is_prefix_secure() {
                self.0.lemma_prefix_secure(s1, s2);
                self.1.lemma_prefix_secure(s1, s2);
            }
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        match v {
            Either::Left(v) => {
                self.0.theorem_serialize_parse_roundtrip(v);
            },
            Either::Right(v) => {
                self.1.theorem_serialize_parse_roundtrip(v);
                let buf = self.1.spec_serialize(v).unwrap();
                if self.1.spec_disjoint_from(&self.0) {
                    self.1.spec_parse_disjoint_on(&self.0, buf);
                }
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, v)) = self.0.spec_parse(buf) {
            self.0.theorem_parse_serialize_roundtrip(buf);
        } else {
            if let Ok((n, v)) = self.1.spec_parse(buf) {
                self.1.theorem_parse_serialize_roundtrip(buf);
            }
        }
    }
}

impl<Fst, Snd> Combinator for OrdChoice<Fst, Snd> where
    Fst: Combinator,
    Snd: Combinator + DisjointFrom<Fst>,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V> + SpecDisjointFrom<Fst::V>,
 {
    type Result<'a> = Either<Fst::Result<'a>, Snd::Result<'a>>;

    type Owned = Either<Fst::Owned, Snd::Owned>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        Fst::exec_is_prefix_secure() && Snd::exec_is_prefix_secure()
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && self.1.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if self.1.disjoint_from(&self.0) {
            if let Ok((n, v)) = self.0.parse(s) {
                Ok((n, Either::Left(v)))
            } else {
                if let Ok((n, v)) = self.1.parse(s) {
                    Ok((n, Either::Right(v)))
                } else {
                    Err(())
                }
            }
        } else {
            Err(())
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && self.1.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        (),
    >) {
        if self.1.disjoint_from(&self.0) {
            match v {
                Either::Left(v) => {
                    let n = self.0.serialize(v, data, pos)?;
                    if n <= usize::MAX - pos && n + pos <= data.len() {
                        Ok(n)
                    } else {
                        Err(())
                    }
                },
                Either::Right(v) => {
                    let n = self.1.serialize(v, data, pos)?;
                    if n <= usize::MAX - pos && n + pos <= data.len() {
                        Ok(n)
                    } else {
                        Err(())
                    }
                },
            }
        } else {
            Err(())
        }
    }
}

//
} // verus!
