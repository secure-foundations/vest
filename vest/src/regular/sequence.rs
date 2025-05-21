use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Spec version of [`Pair`].
pub struct SpecPair<Fst, Snd> where Fst: SecureSpecCombinator, Snd: SpecCombinator {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: spec_fn(Fst::Type) -> Snd,
}

impl<Fst, Snd> SpecCombinator for SpecPair<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator,
 {
    type Type = (Fst::Type, Snd::Type);

    open spec fn requires(&self) -> bool {
        &&& Fst::is_prefix_secure()
        &&& self.fst.requires()
        &&& forall|i: Fst::Type| #[trigger] (self.snd)(i).requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        &&& self.fst.wf(v.0)
        &&& (self.snd)(v.0).wf(v.1)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Some((m, v2)) = snd.spec_parse(s.skip(n as int)) {
                Some((n + m, (v1, v2)))
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        let snd = (self.snd)(v.0);
        let buf1 = self.fst.spec_serialize(v.0);
        let buf2 = snd.spec_serialize(v.1);
        buf1 + buf2
    }
}

impl<Fst, Snd> SecureSpecCombinator for SpecPair<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator,
 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let buf = self.spec_serialize(v);
        let buf0 = self.fst.spec_serialize(v.0);
        let buf1 = (self.snd)(v.0).spec_serialize(v.1);
        self.fst.theorem_serialize_parse_roundtrip(v.0);
        self.fst.lemma_prefix_secure(buf0, buf1);
        (self.snd)(v.0).theorem_serialize_parse_roundtrip(v.1);
        assert((buf0 + buf1).subrange(buf0.len() as int, buf.len() as int) == buf1);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((nm, (v0, v1))) = self.spec_parse(buf) {
            let (n, v0_) = self.fst.spec_parse(buf).unwrap();
            self.fst.lemma_parse_length(buf);
            let buf0 = buf.take(n);
            let buf1 = buf.skip(n);
            assert(buf == buf0 + buf1);
            self.fst.theorem_parse_serialize_roundtrip(buf);
            let (m, v1_) = (self.snd)(v0).spec_parse(buf1).unwrap();
            (self.snd)(v0).theorem_parse_serialize_roundtrip(buf1);
            (self.snd)(v0).lemma_parse_length(buf1);
            let buf2 = self.spec_serialize((v0, v1));
            assert(buf2 == buf.take(nm as int));
        } else {
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            if let Some((nm, (v0, v1))) = self.spec_parse(buf) {
                let (n, _) = self.fst.spec_parse(buf).unwrap();
                self.fst.lemma_parse_length(buf);
                let buf0 = buf.subrange(0, n as int);
                let buf1 = buf.subrange(n as int, buf.len() as int);
                self.fst.lemma_prefix_secure(buf0, buf1);
                self.fst.lemma_prefix_secure(buf0, buf1.add(s2));
                self.fst.lemma_prefix_secure(buf, s2);
                let snd = (self.snd)(v0);
                let (m, v1_) = snd.spec_parse(buf1).unwrap();
                assert(buf.add(s2).subrange(0, n as int) == buf0);
                assert(buf.add(s2).subrange(n as int, buf.add(s2).len() as int) == buf1.add(s2));
                snd.lemma_prefix_secure(buf1, s2);
            } else {
            }
        } else {
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Some((m, v2)) = snd.spec_parse(s.subrange(n as int, s.len() as int)) {
                self.fst.lemma_parse_length(s);
                snd.lemma_parse_length(s.subrange(n as int, s.len() as int));
            }
        }
    }

    open spec fn is_productive(&self) -> bool {
        ||| self.fst.is_productive()
        ||| forall|v1| #[trigger] ((self.snd)(v1)).is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Some((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Some((m, v2)) = snd.spec_parse(s.skip(n as int)) {
                self.fst.lemma_parse_productive(s);
                snd.lemma_parse_productive(s.skip(n as int));
                self.fst.lemma_parse_length(s);
                snd.lemma_parse_length(s.skip(n as int));
            }
        }
    }
}

/// Use this Continuation trait instead of Fn(Input) -> Output
/// to avoid unsupported Verus features
pub trait Continuation<Input> {
    /// Output type of the continuation
    type Output;

    /// The actual continuation function
    fn apply(&self, i: Input) -> (o: Self::Output)
        requires
            self.requires(i),
        ensures
            self.ensures(i, o),
    ;

    /// The precondition of the continuation
    spec fn requires(&self, i: Input) -> bool;

    /// The postcondition of the continuation
    spec fn ensures(&self, i: Input, o: Self::Output) -> bool;
}

/// Combinator that sequentially applies two combinators, where the second combinator depends on
/// the result of the first one.
pub struct Pair<Fst, FstT: View, Snd: View, Cont> {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: Cont,
    /// spec closure for continuation well-formedness
    pub spec_snd: Ghost<spec_fn(FstT::V) -> Snd::V>,
}

impl<Fst, FsrT, Snd, Cont> View for Pair<Fst, FsrT, Snd, Cont> where
    Fst: View,
    FsrT: View,
    Snd: View,
    Fst::V: SecureSpecCombinator<Type = FsrT::V>,
    Snd::V: SpecCombinator,
 {
    type V = SpecPair<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        let Ghost(spec_snd) = self.spec_snd;
        SpecPair { fst: self.fst@, snd: spec_snd }
    }
}

impl<'x, I, O, Fst, Snd, Cont> Combinator<'x, I, O> for Pair<Fst, Fst::Type, Snd, Cont> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O, SType = &'x <Fst as Combinator<'x, I, O>>::Type>,
    Snd: Combinator<'x, I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    Cont: for <'a>Continuation<&'a Fst::Type, Output = Snd>,
    <Fst as Combinator<'x, I, O>>::Type: 'x,
 {
    type Type = (Fst::Type, Snd::Type);

    type SType = (Fst::SType, Snd::SType);

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn ex_requires(&self) -> bool {
        let Ghost(spec_snd_dep) = self.spec_snd;
        &&& self.fst.ex_requires()
        &&& forall|i| #[trigger] self.snd.requires(i)
        &&& forall|i, snd| #[trigger]
            self.snd.ensures(i, snd) ==> snd.ex_requires() && snd@ == spec_snd_dep(i@)
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v1) = self.fst.parse(s.clone())?;
        proof {
            self@.fst.lemma_parse_length(s@);
        }
        let s_ = s.subrange(n, s.len());
        let snd = self.snd.apply(&v1);
        let (m, v2) = snd.parse(s_)?;
        proof {
            snd@.lemma_parse_length(s@.skip(n as int));
        }
        Ok((n + m, (v1, v2)))
        // if let Some(nm) = n.checked_add(m) {
        //     Ok((nm, (v1, v2)))
        // } else {
        //     Err(ParseError::SizeOverflow)
        // }

    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let snd = self.snd.apply(v.0);
        let n = self.fst.serialize(v.0, data, pos)?;
        let m = snd.serialize(v.1, data, pos + n)?;
        if let Some(nm) = n.checked_add(m) {
            assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@)));
            Ok(nm)
        } else {
            Err(SerializeError::SizeOverflow)
        }
    }
}

impl<Fst: SecureSpecCombinator, Snd: SpecCombinator> SpecCombinator for (Fst, Snd) {
    type Type = (Fst::Type, Snd::Type);

    open spec fn requires(&self) -> bool {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.wf(v)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.spec_parse(s)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.spec_serialize(v)
    }
}

impl<Fst: SecureSpecCombinator, Snd: SecureSpecCombinator> SecureSpecCombinator for (Fst, Snd) {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.theorem_serialize_parse_roundtrip(v)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.theorem_parse_serialize_roundtrip(buf)
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.lemma_prefix_secure(buf, s2)
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.lemma_parse_length(s)
    }

    open spec fn is_productive(&self) -> bool {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        SpecPair { fst: self.0, snd: |r: Fst::Type| self.1 }.lemma_parse_productive(s)
    }
}

impl<'x, Fst, Snd, I, O> Combinator<'x, I, O> for (Fst, Snd) where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O>,
    Snd: Combinator<'x, I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
 {
    type Type = (Fst::Type, Snd::Type);

    type SType = (Fst::SType, Snd::SType);

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

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires() && self.1.ex_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v1) = self.0.parse(s.clone())?;
        proof {
            self@.0.lemma_parse_length(s@);
        }
        let s_ = s.subrange(n, s.len());
        let (m, v2) = self.1.parse(s_)?;
        proof {
            self.1@.lemma_parse_length(s@.skip(n as int));
        }
        Ok((n + m, (v1, v2)))
    }

    fn serialize(&self, v: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let n = self.0.serialize(v.0, data, pos)?;
        let m = self.1.serialize(v.1, data, pos + n)?;
        if m <= usize::MAX - n {
            assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@)));
            Ok(n + m)
        } else {
            Err(SerializeError::SizeOverflow)
        }
    }
}

/// Combinator that sequentially applies two combinators and returns the result of the second one.
pub struct Preceded<Fst, Snd>(pub Fst, pub Snd);

impl<Fst: View, Snd: View> View for Preceded<Fst, Snd> {
    type V = Preceded<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        Preceded(self.0@, self.1@)
    }
}

impl<Fst: SecureSpecCombinator<Type = ()>, Snd: SpecCombinator> SpecCombinator for Preceded<
    Fst,
    Snd,
> {
    type Type = Snd::Type;

    open spec fn requires(&self) -> bool {
        (self.0, self.1).requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        (self.0, self.1).wf(((), v))
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, ((), v))) = (self.0, self.1).spec_parse(s) {
            Some((n, v))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (self.0, self.1).spec_serialize(((), v))
    }
}

impl<
    Fst: SecureSpecCombinator<Type = ()>,
    Snd: SecureSpecCombinator,
> SecureSpecCombinator for Preceded<Fst, Snd> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (self.0, self.1).theorem_serialize_parse_roundtrip(((), v));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, ((), v))) = (self.0, self.1).spec_parse(buf) {
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

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, ((), v))) = (self.0, self.1).spec_parse(s) {
            (self.0, self.1).lemma_parse_length(s);
        }
    }

    open spec fn is_productive(&self) -> bool {
        (self.0, self.1).is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Some((n, ((), v))) = (self.0, self.1).spec_parse(s) {
            (self.0, self.1).lemma_parse_productive(s);
        }
    }
}

impl<'x, I, O, Fst, Snd> Combinator<'x, I, O> for Preceded<Fst, Snd> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O, Type = (), SType = ()>,
    Snd: Combinator<'x, I, O>,
    Fst::V: SecureSpecCombinator<Type = ()>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
 {
    type Type = Snd::Type;

    type SType = Snd::SType;

    open spec fn spec_length(&self) -> Option<usize> {
        (self.0, self.1).spec_length()
    }

    fn length(&self) -> Option<usize> {
        (&self.0, &self.1).length()
    }

    open spec fn ex_requires(&self) -> bool {
        (&self.0, &self.1).ex_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, ((), v)) = (&self.0, &self.1).parse(s.clone())?;
        Ok((n, v))
    }

    fn serialize<'b>(&self, v: Self::SType, data: &'b mut O, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        (&self.0, &self.1).serialize(((), v), data, pos)
    }
}

/// Combinator that sequentially applies two combinators and returns the result of the first one.
pub struct Terminated<Fst, Snd>(pub Fst, pub Snd);

impl<Fst: View, Snd: View> View for Terminated<Fst, Snd> {
    type V = Terminated<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        Terminated(self.0@, self.1@)
    }
}

impl<Fst: SecureSpecCombinator, Snd: SpecCombinator<Type = ()>> SpecCombinator for Terminated<
    Fst,
    Snd,
> {
    type Type = Fst::Type;

    open spec fn requires(&self) -> bool {
        (self.0, self.1).requires()
    }

    open spec fn wf(&self, v: Self::Type) -> bool {
        (self.0, self.1).wf((v, ()))
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        if let Some((n, (v, ()))) = (self.0, self.1).spec_parse(s) {
            Some((n, v))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        (self.0, self.1).spec_serialize((v, ()))
    }
}

impl<
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator<Type = ()>,
> SecureSpecCombinator for Terminated<Fst, Snd> {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        (self.0, self.1).theorem_serialize_parse_roundtrip((v, ()));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((n, (v, ()))) = (self.0, self.1).spec_parse(buf) {
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

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if let Some((n, (v, ()))) = (self.0, self.1).spec_parse(s) {
            (self.0, self.1).lemma_parse_length(s);
        }
    }

    open spec fn is_productive(&self) -> bool {
        (self.0, self.1).is_productive()
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if let Some((n, (v, ()))) = (self.0, self.1).spec_parse(s) {
            (self.0, self.1).lemma_parse_productive(s);
        }
    }
}

impl<'x, I, O, Fst, Snd> Combinator<'x, I, O> for Terminated<Fst, Snd> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<'x, I, O>,
    Snd: Combinator<'x, I, O, Type = (), SType = ()>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = ()>,
 {
    type Type = Fst::Type;

    type SType = Fst::SType;

    open spec fn spec_length(&self) -> Option<usize> {
        (self.0, self.1).spec_length()
    }

    fn length(&self) -> Option<usize> {
        (&self.0, &self.1).length()
    }

    open spec fn ex_requires(&self) -> bool {
        (&self.0, &self.1).ex_requires()
    }

    fn parse(&self, s: I) -> Result<(usize, Self::Type), ParseError> {
        let (n, (v, ())) = (&self.0, &self.1).parse(s.clone())?;
        Ok((n, v))
    }

    fn serialize<'b>(&self, v: Self::SType, data: &'b mut O, pos: usize) -> Result<
        usize,
        SerializeError,
    > {
        (&self.0, &self.1).serialize((v, ()), data, pos)
    }
}

} // verus!
