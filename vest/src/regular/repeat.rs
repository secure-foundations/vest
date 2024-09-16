use crate::properties::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

/// A combinator to repeatedly parse/serialize the inner combinator C
/// until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer, Repeat fails
pub struct Repeat<C>(pub C);

/// Wrappers around Vec so that their View's can be implemented as DeepView
#[derive(Debug)]
pub struct RepeatResult<'a, C: Combinator>(pub Vec<C::Result<'a>>)
    where <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>;

/// Owned version of RepeatResult
#[derive(Debug)]
pub struct RepeatResultOwned<C: Combinator>(pub Vec<C::Owned>)
    where <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>;

impl<C: View> View for Repeat<C>
{
    type V = Repeat<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        Repeat(self.0@)
    }
}

impl<C: Combinator> View for RepeatResultOwned<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    type V = Seq<<C::Owned as View>::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

impl<'a, C: Combinator> View for RepeatResult<'a, C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    type V = Seq<<C::Owned as View>::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

impl<C: SpecCombinator + SecureSpecCombinator> SpecCombinator for Repeat<C> {
    type SpecResult = Seq<C::SpecResult>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
        decreases s.len()
    {
        if !C::spec_is_prefix_secure() {
            Err(())
        } else if s.len() == 0 {
            Ok((0, seq![]))
        } else {
            match self.0.spec_parse(s) {
                Ok((n, v)) =>
                    if 0 < n <= s.len() {
                        match self.spec_parse(s.skip(n as int)) {
                            Ok((_, vs)) => Ok((s.len() as usize, seq![v] + vs)),
                            Err(..) => Err(()),
                        }
                    } else {
                        Err(())
                    }
                Err(..) => Err(()),
            }
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>
        decreases v.len()
    {
        if !C::spec_is_prefix_secure() {
            Err(())
        } else if v.len() == 0 {
            Ok(seq![])
        } else {
            match self.0.spec_serialize(v[0]) {
                Ok(s) =>
                    if s.len() != 0 {
                        match self.spec_serialize(v.drop_first()) {
                            Ok(rest) =>
                                if s.len() + rest.len() <= usize::MAX {
                                    Ok(s + rest)
                                } else {
                                    Err(())
                                }
                            Err(..) => Err(()),
                        }
                    } else {
                        Err(())
                    }
                Err(..) => Err(()),
            }
        }
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Repeat<C> {
    /// Prepending bytes to the buffer may result in more items parsed
    /// so Repeat is not prefix secure
    open spec fn spec_is_prefix_secure() -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult)
        decreases v.len()
    {
        if v.len() == 0 {
            assert(self.spec_serialize(v) matches Ok(b) ==> self.spec_parse(b).unwrap() =~= (0, v));
        } else {
            if self.spec_serialize(v).is_ok() {
                let s = self.0.spec_serialize(v[0]).unwrap();
                let rest = self.spec_serialize(v.drop_first()).unwrap();

                self.theorem_serialize_parse_roundtrip(v.drop_first());
                self.0.theorem_serialize_parse_roundtrip(v[0]);

                // Some technical assumptions (e.g. C should not parse a different
                // value when the buffer is extended with more bytes)
                if C::spec_is_prefix_secure() && s.len() + rest.len() <= usize::MAX {
                    self.0.lemma_prefix_secure(s, rest);
                    let (n, _) = self.0.spec_parse(s + rest).unwrap();
                    self.0.spec_parse_wf(s + rest);

                    assert((s + rest).skip(n as int) =~= rest);
                    assert(seq![v[0]] + v.drop_first() == v);
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases buf.len()
    {
        if buf.len() == 0 {
            let empty: Seq<u8> = seq![];
            assert(buf.subrange(0, 0) =~= empty);
        } else {
            if let Ok((n, v)) = self.spec_parse(buf) {
                let (n1, v1) = self.0.spec_parse(buf).unwrap();
                let (n2, v2) = self.spec_parse(buf.skip(n1 as int)).unwrap();

                self.theorem_parse_serialize_roundtrip(buf.skip(n1 as int));
                self.0.theorem_parse_serialize_roundtrip(buf);

                if C::spec_is_prefix_secure() {
                    assert(v2 == v.drop_first());
                    assert(buf.subrange(0, n1 as int) + buf.skip(n1 as int).subrange(0, n2 as int) == buf.subrange(0, n as int));
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {}
}

impl<C: Combinator> Repeat<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    pub open spec fn deep_view<'a>(v: &'a [C::Result<'a>]) -> Seq<<C::Owned as View>::V> {
        Seq::new(v.len() as nat, |i: int| v@[i]@)
    }

    /// Helper function for parse()
    /// TODO: Recursion is not ideal, but hopefully tail call opt will kick in
    fn parse_helper<'a>(&self, s: &'a [u8], res: &mut Vec<C::Result<'a>>) -> (suc: bool)
        requires
            self.0.parse_requires(),
            <C as View>::V::spec_is_prefix_secure(),

        ensures
            suc ==> {
                &&& self@.spec_parse(s@) is Ok
                &&& self@.spec_parse(s@) matches Ok((n, v)) ==>
                    RepeatResult::<C>(*res)@ =~= RepeatResult::<C>(*old(res))@ + v
            },
            !suc ==> self@.spec_parse(s@) is Err
    {
        if s.len() == 0 {
            return true;
        }

        if let Ok((n, v)) = self.0.parse(s) {
            if n > 0 {
                res.push(v);
                return self.parse_helper(slice_subrange(s, n, s.len()), res);
            }
        }

        return false;
    }

    fn serialize_helper(&self, v: &mut RepeatResult<'_, C>, data: &mut Vec<u8>, pos: usize, len: usize) -> (res: Option<usize>)
        requires
            self.0.serialize_requires(),
            <C as View>::V::spec_is_prefix_secure(),

        ensures
            data@.len() == old(data)@.len(),
            res matches Some(n) ==> {
                &&& self@.spec_serialize(old(v)@) is Ok
                &&& self@.spec_serialize(old(v)@) matches Ok(s) ==>
                    n == (len + s.len()) && data@ =~= seq_splice(old(data)@, (pos + len) as usize, s)
            },
    {
        if pos > usize::MAX - len || pos + len >= data.len() {
            return None;
        }

        if v.0.len() == 0 {
            assert(data@ =~= seq_splice(old(data)@, pos, seq![]));
            return Some(len);
        }

        if let Ok(n1) = self.0.serialize(v.0.remove(0), data, pos + len) {
            assert(v@ =~= old(v)@.drop_first());

            if n1 != 0 {
                let ghost data2 = data@;

                if let Some(next_len) = len.checked_add(n1) {
                    return self.serialize_helper(v, data, pos, next_len);
                }
            }
        }

        None
    }
}

impl<C: Combinator> Combinator for Repeat<C> where
    <C as View>::V: SecureSpecCombinator<SpecResult = <C::Owned as View>::V>,
{
    type Result<'a> = RepeatResult<'a, C>;
    type Owned = RepeatResultOwned<C>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    fn exec_is_prefix_secure() -> bool {
        false
    }

    open spec fn parse_requires(&self) -> bool {
        &&& <C as View>::V::spec_is_prefix_secure()
        &&& self.0.parse_requires()
    }

    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ()>) {
        let mut res = Vec::new();

        if self.parse_helper(s, &mut res) {
            Ok((s.len(), RepeatResult(res)))
        } else {
            Err(())
        }
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::spec_is_prefix_secure()
        &&& self.0.serialize_requires()
    }

    fn serialize(&self, mut v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, ()>) {
        if let Some(n) = self.serialize_helper(&mut v, data, pos, 0) {
            assert(v@.skip(0) == v@);
            Ok(n)
        } else {
            Err(())
        }
    }
}

}
