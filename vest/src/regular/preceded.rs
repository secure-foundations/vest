use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// Combinator that sequentially applies two combinators and returns the result of the second one.
pub struct Preceded<Fst, Snd>(pub Fst, pub Snd);

impl<Fst, Snd> View for Preceded<
    Fst,
    Snd,
> where
    Fst: for<'a> Combinator<Result<'a> = (), Owned = ()>,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = ()>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
 {
    type V = Preceded<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        Preceded(self.0@, self.1@)
    }
}

impl<Fst: SecureSpecCombinator<SpecResult = ()>, Snd: SpecCombinator> SpecCombinator for Preceded<
    Fst,
    Snd,
> {
    type SpecResult = Snd::SpecResult;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        if Fst::is_prefix_secure() {
            if let Ok((n, ())) = self.0.spec_parse(s) {
                if let Ok((m, v)) = self.1.spec_parse(s.subrange(n as int, s.len() as int)) {
                    Ok(((n + m) as usize, v))
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, ())) = self.0.spec_parse(s) {
            if let Ok((m, v)) = self.1.spec_parse(s.subrange(n as int, s.len() as int)) {
                self.0.spec_parse_wf(s);
                self.1.spec_parse_wf(s.subrange(n as int, s.len() as int));
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if Fst::is_prefix_secure() {
            if let Ok(buf1) = self.0.spec_serialize(()) {
                if let Ok(buf2) = self.1.spec_serialize(v) {
                    if buf1.len() + buf2.len() <= usize::MAX {
                        Ok(buf1.add(buf2))
                    } else {
                        Err(())
                    }
                } else {
                    Err(())
                }
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }
}

impl<
    Fst: SecureSpecCombinator<SpecResult = ()>,
    Snd: SecureSpecCombinator,
> SecureSpecCombinator for Preceded<Fst, Snd> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok((buf)) = self.spec_serialize(v) {
            let buf0 = self.0.spec_serialize(()).unwrap();
            let buf1 = self.1.spec_serialize(v).unwrap();
            self.0.theorem_serialize_parse_roundtrip(());
            self.0.lemma_prefix_secure(buf0, buf1);
            self.1.theorem_serialize_parse_roundtrip(v);
            assert(buf0.add(buf1).subrange(buf0.len() as int, buf.len() as int) == buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((nm, v)) = self.spec_parse(buf) {
            let (n, _) = self.0.spec_parse(buf).unwrap();
            self.0.spec_parse_wf(buf);
            let buf0 = buf.subrange(0, n as int);
            let buf1 = buf.subrange(n as int, buf.len() as int);
            assert(buf == buf0.add(buf1));
            self.0.lemma_prefix_secure(buf0, buf1);
            self.0.theorem_parse_serialize_roundtrip(buf);
            let (m, v_) = self.1.spec_parse(buf1).unwrap();
            self.1.theorem_parse_serialize_roundtrip(buf1);
            self.1.spec_parse_wf(buf1);
            let buf2 = self.spec_serialize(v).unwrap();
            assert(buf2 == buf.subrange(0, nm as int));
        } else {
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            if let Ok((nm, v)) = self.spec_parse(buf) {
                let (n, _) = self.0.spec_parse(buf).unwrap();
                self.0.spec_parse_wf(buf);
                let buf0 = buf.subrange(0, n as int);
                let buf1 = buf.subrange(n as int, buf.len() as int);
                self.0.lemma_prefix_secure(buf0, buf1);
                self.0.lemma_prefix_secure(buf0, buf1.add(s2));
                self.0.lemma_prefix_secure(buf, s2);
                let (m, v_) = self.1.spec_parse(buf1).unwrap();
                assert(buf.add(s2).subrange(0, n as int) == buf0);
                assert(buf.add(s2).subrange(n as int, buf.add(s2).len() as int) == buf1.add(s2));
                self.1.lemma_prefix_secure(buf1, s2);
            } else {
            }
        } else {
        }
    }
}

impl<Fst, Snd> Combinator for Preceded<
    Fst,
    Snd,
> where
    Fst: for<'a> Combinator<Result<'a> = (), Owned = ()>,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = ()>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
 {
    type Result<'a> = Snd::Result<'a>;

    type Owned = Snd::Owned;

    open spec fn spec_length(&self) -> Option<usize> {
        if let Some(n) = self.0.spec_length() {
            if let Some(m) = self.1.spec_length() {
                if n <= usize::MAX - m {
                    Some((n + m) as usize)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    fn length(&self) -> Option<usize> {
        if let Some(n) = self.0.length() {
            if let Some(m) = self.1.length() {
                if n <= usize::MAX - m {
                    Some(n + m)
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && self.1.parse_requires() && Fst::V::is_prefix_secure()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (n, ()): (usize, ()) = self.0.parse(s)?;
        let s_ = slice_subrange(s, n, s.len());
        let (m, v) = self.1.parse(s_)?;
        if n <= usize::MAX - m {
            Ok(((n + m), v))
        } else {
            Err(ParseError::SizeOverflow)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && self.1.serialize_requires() && Fst::V::is_prefix_secure()
    }

    fn serialize<'b>(&self, v: Self::Result<'_>, data: &'b mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let n = self.0.serialize((), data, pos)?;
        if n <= usize::MAX - pos && n + pos <= data.len() {
            let m = self.1.serialize(v, data, pos + n)?;
            if m <= usize::MAX - n {
                assert(data@.subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                    v@,
                ).unwrap());
                assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
                Ok(n + m)
            } else {
                Err(SerializeError::SizeOverflow)
            }
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
