use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

use super::depend::*;

verus! {

/// Use this Continuation trait instead of Fn(Input) -> Output
/// to avoid unsupported Verus features
pub trait Continuation {
    /// Input type of the continuation (e.g. C::Result<'a> of another combinator C)
    type Input<'a>;

    /// Output type of the continuation
    type Output;

    /// The actual continuation function
    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output)
        requires self.requires(i)
        ensures self.ensures(i, o);

    spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool;
    spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool;
}

/// Combinator that sequentially applies two combinators, where the second combinator depends on
/// the result of the first one.
#[verifier::reject_recursive_types(Snd)]
pub struct DependCont<Fst, Snd, C> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    C: for <'a>Continuation<Input<'a> = Fst::Result<'a>, Output = Snd>,
 {
    /// combinators that contain dependencies
    pub fst: Fst,
    /// closure that captures dependencies and maps them to the dependent combinators
    // Replaces `for <'a>fn(Fst::Result<'a>) -> Snd` in Depend,
    pub snd: C,
    /// spec closure for well-formedness
    pub spec_snd: Ghost<spec_fn(<Fst::Owned as View>::V) -> Snd::V>,
}

impl<Fst, Snd, C> DependCont<Fst, Snd, C> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    C: for <'a>Continuation<Input<'a> = Fst::Result<'a>, Output = Snd>,
 {
    /// well-formed [`DepPair`] should have its clousre [`snd`] well-formed w.r.t. [`spec_snd`]
    pub open spec fn wf(&self) -> bool {
        let Ghost(spec_snd_dep) = self.spec_snd;
        &&& forall|i| #[trigger] self.snd.requires(i)
        &&& forall|i, snd| self.snd.ensures(i, snd) ==> spec_snd_dep(i@) == snd@
    }
}

/// Same [`View`] as [`Depend`]
impl<Fst, Snd, C> View for DependCont<Fst, Snd, C> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    C: for <'a>Continuation<Input<'a> = Fst::Result<'a>, Output = Snd>,
 {
    type V = SpecDepend<Fst::V, Snd::V>;

    open spec fn view(&self) -> Self::V {
        let Ghost(spec_snd) = self.spec_snd;
        SpecDepend { fst: self.fst@, snd: spec_snd }
    }
}

/// Same impl as [`Depend`], except that snd is a [`Continuation`] instead of an `Fn`
impl<Fst, Snd, C> Combinator for DependCont<Fst, Snd, C> where
    Fst: Combinator,
    Snd: Combinator,
    Fst::V: SecureSpecCombinator<SpecResult = <Fst::Owned as View>::V>,
    Snd::V: SecureSpecCombinator<SpecResult = <Snd::Owned as View>::V>,
    C: for <'a>Continuation<Input<'a> = Fst::Result<'a>, Output = Snd>,
    for <'a>Fst::Result<'a>: Copy,
 {
    type Result<'a> = (Fst::Result<'a>, Snd::Result<'a>);

    type Owned = (Fst::Owned, Snd::Owned);

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
        &&& self.wf()
        &&& self.fst.parse_requires()
        &&& forall |i, snd| self.snd.ensures(i, snd) ==> snd.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        if Fst::exec_is_prefix_secure() {
            let (n, v1) = self.fst.parse(s)?;
            let s_ = slice_subrange(s, n, s.len());
            let snd = self.snd.apply(v1);
            let (m, v2) = snd.parse(s_)?;
            if n <= usize::MAX - m {
                Ok(((n + m), (v1, v2)))
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.wf()
        &&& self.fst.serialize_requires()
        &&& forall |i, snd| self.snd.ensures(i, snd) ==> snd.serialize_requires()
    }

    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<
        usize,
        (),
    >) {
        if Fst::exec_is_prefix_secure() {
            let n = self.fst.serialize(v.0, data, pos)?;
            if n <= usize::MAX - pos && n + pos <= data.len() {
                let snd = self.snd.apply(v.0);
                let m = snd.serialize(v.1, data, pos + n)?;
                if m <= usize::MAX - n {
                    assert(data@.subrange(pos as int, pos + n + m as int) == self@.spec_serialize(
                        v@,
                    ).unwrap());
                    assert(data@ == seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));
                    Ok(n + m)
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

}
