use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Spec version of [`Depend`].
pub struct SpecDepend<Fst, Snd> where Fst: SecureSpecCombinator, Snd: SpecCombinator {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    pub snd: spec_fn(Fst::Type) -> Snd,
}

impl<Fst, Snd> SpecCombinator for SpecDepend<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SpecCombinator,
 {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        if Fst::is_prefix_secure() {
            if let Ok((n, v1)) = self.fst.spec_parse(s) {
                let snd = (self.snd)(v1);
                if let Ok((m, v2)) = snd.spec_parse(s.subrange(n as int, s.len() as int)) {
                    if n <= usize::MAX - m {
                        Ok(((n + m) as usize, (v1, v2)))
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

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        if let Ok((n, v1)) = self.fst.spec_parse(s) {
            let snd = (self.snd)(v1);
            if let Ok((m, v2)) = snd.spec_parse(s.subrange(n as int, s.len() as int)) {
                self.fst.spec_parse_wf(s);
                snd.spec_parse_wf(s.subrange(n as int, s.len() as int));
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        if Fst::is_prefix_secure() {
            let snd = (self.snd)(v.0);
            if let Ok(buf1) = self.fst.spec_serialize(v.0) {
                if let Ok(buf2) = snd.spec_serialize(v.1) {
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

impl<Fst, Snd> SecureSpecCombinator for SpecDepend<Fst, Snd> where
    Fst: SecureSpecCombinator,
    Snd: SecureSpecCombinator,
 {
    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if let Ok((buf)) = self.spec_serialize(v) {
            let buf0 = self.fst.spec_serialize(v.0).unwrap();
            let buf1 = (self.snd)(v.0).spec_serialize(v.1).unwrap();
            self.fst.theorem_serialize_parse_roundtrip(v.0);
            self.fst.lemma_prefix_secure(buf0, buf1);
            (self.snd)(v.0).theorem_serialize_parse_roundtrip(v.1);
            assert(buf0.add(buf1).subrange(buf0.len() as int, buf.len() as int) == buf1);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
            let (n, v0_) = self.fst.spec_parse(buf).unwrap();
            self.fst.spec_parse_wf(buf);
            let buf0 = buf.subrange(0, n as int);
            let buf1 = buf.subrange(n as int, buf.len() as int);
            assert(buf == buf0.add(buf1));
            self.fst.theorem_parse_serialize_roundtrip(buf);
            let (m, v1_) = (self.snd)(v0).spec_parse(buf1).unwrap();
            (self.snd)(v0).theorem_parse_serialize_roundtrip(buf1);
            (self.snd)(v0).spec_parse_wf(buf1);
            let buf2 = self.spec_serialize((v0, v1)).unwrap();
            assert(buf2 == buf.subrange(0, nm as int));
        } else {
        }
    }

    open spec fn is_prefix_secure() -> bool {
        Fst::is_prefix_secure() && Snd::is_prefix_secure()
    }

    proof fn lemma_prefix_secure(&self, buf: Seq<u8>, s2: Seq<u8>) {
        if Fst::is_prefix_secure() && Snd::is_prefix_secure() {
            if let Ok((nm, (v0, v1))) = self.spec_parse(buf) {
                let (n, _) = self.fst.spec_parse(buf).unwrap();
                self.fst.spec_parse_wf(buf);
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
#[verifier::reject_recursive_types(Snd)]
pub struct Depend<I, O, Fst, Snd, C> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    C: for <'a>Continuation<&'a Fst::Type, Output = Snd>,
 {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    // Replaces `for fn(Fst::Result) -> Snd` in Depend,
    pub snd: C,
    /// spec closure for well-formedness
    pub spec_snd: Ghost<spec_fn(<Fst::Type as View>::V) -> Snd::V>,
}

impl<I, O, Fst, Snd, C> Depend<I, O, Fst, Snd, C> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    C: for <'a>Continuation<&'a Fst::Type, Output = Snd>,
 {
    /// well-formed [`DepPair`] should have its clousre [`snd`] well-formed w.r.t. [`spec_snd`]
    pub open spec fn wf(&self) -> bool {
        let Ghost(spec_snd_dep) = self.spec_snd;
        &&& forall|i| #[trigger] self.snd.requires(i)
        &&& forall|i, snd| self.snd.ensures(i, snd) ==> spec_snd_dep(i@) == snd@
    }
}

/// Same [`View`] as [`Depend`]
impl<I, O, Fst, Snd, C> View for Depend<I, O, Fst, Snd, C> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    C: for <'a>Continuation<&'a Fst::Type, Output = Snd>,
 {
    type V = SpecDepend<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        let Ghost(spec_snd) = self.spec_snd;
        SpecDepend { fst: self.fst@, snd: spec_snd }
    }
}

/// Same impl as [`Depend`], except that snd is a [`Continuation`] instead of an `Fn`
impl<I, O, Fst, Snd, C> Combinator<I, O> for Depend<I, O, Fst, Snd, C> where
    I: VestInput,
    O: VestOutput<I>,
    Fst: Combinator<I, O>,
    Snd: Combinator<I, O>,
    Fst::V: SecureSpecCombinator<Type = <Fst::Type as View>::V>,
    Snd::V: SecureSpecCombinator<Type = <Snd::Type as View>::V>,
    C: for <'a>Continuation<&'a Fst::Type, Output = Snd>,
 {
    type Type = (Fst::Type, Snd::Type);

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.wf()
        &&& self.fst.parse_requires()
        &&& Fst::V::is_prefix_secure()
        &&& forall|i, snd| self.snd.ensures(i, snd) ==> snd.parse_requires()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (n, v1) = self.fst.parse(s.clone())?;
        let s_ = s.subrange(n, s.len());
        let snd = self.snd.apply(&v1);
        let (m, v2) = snd.parse(s_)?;
        if let Some(nm) = n.checked_add(m) {
            Ok((nm, (v1, v2)))
        } else {
            Err(ParseError::SizeOverflow)
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.wf()
        &&& self.fst.serialize_requires()
        &&& Fst::V::is_prefix_secure()
        &&& forall|i, snd| self.snd.ensures(i, snd) ==> snd.serialize_requires()
    }

    fn serialize(&self, v: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let snd = self.snd.apply(&v.0);
        let n = self.fst.serialize(v.0, data, pos)?;
        if n <= usize::MAX - pos && n + pos <= data.len() {
            let m = snd.serialize(v.1, data, pos + n)?;
            if let Some(nm) = n.checked_add(m) {
                assert(data@.subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                    v@,
                ).unwrap());
                assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
                Ok(nm)
            } else {
                Err(SerializeError::SizeOverflow)
            }
        } else {
            Err(SerializeError::InsufficientBuffer)
        }
    }
}

} // verus!
