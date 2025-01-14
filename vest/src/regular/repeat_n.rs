use super::repeat::RepeatResult;
use crate::properties::*;
use vstd::prelude::*;

verus! {

/// Combinator that repeats [C] combinator [self.1] times.
pub struct RepeatN<C>(pub C, pub usize);

impl<C: View> View for RepeatN<C> {
    type V = RepeatN<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        RepeatN(self.0@, self.1)
    }
}

impl<C: SecureSpecCombinator> RepeatN<C> {
    /// Helper function for parsing [n] instances of [C] from [s].
    pub closed spec fn spec_parse_helper(&self, s: Seq<u8>, n: usize) -> Result<
        (usize, Seq<C::Type>),
        (),
    >
        decreases n,
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if n == 0 {
            Ok((0, seq![]))
        } else {
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Ok((m, vs)) => match self.0.spec_parse(s.skip(m as int)) {
                    Ok((k, v)) => if m + k <= usize::MAX {
                        Ok(((m + k) as usize, vs.push(v)))
                    } else {
                        Err(())
                    },
                    Err(..) => Err(()),
                },
                Err(..) => Err(()),
            }
        }
    }

    /// Helper function for serializing [n] instances of [C] from [v].
    pub closed spec fn spec_serialize_helper(&self, v: Seq<C::Type>, n: usize) -> Result<
        Seq<u8>,
        (),
    >
        decreases n,
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if v.len() != n {
            Err(())
        } else if n == 0 {
            Ok(seq![])
        } else {
            match self.spec_serialize_helper(v.drop_last(), (n - 1) as usize) {
                Ok(ss) => match self.0.spec_serialize(v.last()) {
                    Ok(s) => if s.len() + ss.len() <= usize::MAX {
                        Ok(ss + s)
                    } else {
                        Err(())
                    },
                    Err(..) => Err(()),
                },
                Err(..) => Err(()),
            }
        }
    }

    proof fn lemma_spec_parse_err_unrecoverable(&self, s: Seq<u8>, n1: usize, n2: usize)
        ensures
            n1 <= n2 ==> self.spec_parse_helper(s, n1) is Err ==> self.spec_parse_helper(
                s,
                n2,
            ) is Err,
        decreases n2,
    {
        if n2 == n1 {
        } else if n2 > n1 {
            self.lemma_spec_parse_err_unrecoverable(s, n1, (n2 - 1) as usize);
        }
    }
    // proof fn lemma_spec_serialize_err_unrecoverable(
    //     &self,
    //     v1: Seq<C::SpecResult>,
    //     v2: Seq<C::SpecResult>,
    //     n1: usize,
    //     n2: usize,
    // )
    //     requires
    //         v1.len() == n1,
    //         v2.len() == n2,
    //         v1 == v2.take(n1 as int),
    //     ensures
    //         n1 <= n2 ==> self.spec_serialize_helper(v1, n1) is Err ==> self.spec_serialize_helper(
    //             v2,
    //             n2,
    //         ) is Err,
    //     decreases n2,
    // {
    //     if n2 == n1 {
    //         assert(v1 =~= v2);
    //     } else if n2 > n1 {
    //         assert(v1 =~= v2.drop_last().take(n1 as int));
    //         self.lemma_spec_serialize_err_unrecoverable(v1, v2.drop_last(), n1, (n2 - 1) as usize);
    //     }
    // }

}

impl<C: SecureSpecCombinator> RepeatN<C> {
    proof fn theorem_serialize_parse_roundtrip_helper(&self, v: Seq<C::Type>, n: usize)
        ensures
            self.spec_serialize_helper(v, n) matches Ok(b) ==> self.spec_parse_helper(b, n) == Ok::<
                _,
                (),
            >((b.len() as usize, v)),
        decreases n,
    {
        if v.len() != n {
        } else if n == 0 {
            assert(self.spec_serialize_helper(v, n) matches Ok(b) ==> self.spec_parse_helper(
                b,
                n,
            ).unwrap() == (b.len() as usize, v));
        } else {
            self.theorem_serialize_parse_roundtrip_helper(v.drop_last(), (n - 1) as usize);
            if let Ok(ss) = self.spec_serialize_helper(v.drop_last(), (n - 1) as usize) {
                if let Ok(s) = self.0.spec_serialize(v.last()) {
                    if s.len() + ss.len() <= usize::MAX {
                        self.lemma_prefix_secure_helper(ss, s, (n - 1) as usize);
                        self.0.theorem_serialize_parse_roundtrip(v.last());
                        if let Ok((m, vs)) = self.spec_parse_helper(ss + s, (n - 1) as usize) {
                            assert((ss + s).skip(m as int) == s);
                            if let Ok((k, v_)) = self.0.spec_parse((ss + s).skip(m as int)) {
                                assert(m + k == (ss + s).len());
                                assert(vs.push(v_) == v);
                            }
                        }
                    }
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip_helper(&self, buf: Seq<u8>, n: usize)
        requires
            buf.len() <= usize::MAX,
        ensures
            self.spec_parse_helper(buf, n) matches Ok((m, v)) ==> self.spec_serialize_helper(v, n)
                == Ok::<_, ()>(buf.take(m as int)),
        decreases n,
    {
        if n == 0 {
            assert(self.spec_parse_helper(buf, n) matches Ok((m, v)) ==> self.spec_serialize_helper(
                v,
                n,
            ).unwrap() == buf.take(m as int));
        } else {
            self.lemma_parse_length_helper(buf, n);  // <-- this is the key
            self.theorem_parse_serialize_roundtrip_helper(buf, (n - 1) as usize);
            if let Ok((m, vs)) = self.spec_parse_helper(buf, (n - 1) as usize) {
                if let Ok((k, v)) = self.0.spec_parse(buf.skip(m as int)) {
                    assert(vs.push(v).drop_last() == vs);
                    if m + k <= usize::MAX {
                        self.0.theorem_parse_serialize_roundtrip(buf.skip(m as int));
                        assert(vs.push(v).last() == v);
                        assert(buf.take(m as int) + buf.skip(m as int).take(k as int) == buf.take(
                            (m + k) as int,
                        ));
                    }
                }
            }
        }
    }

    proof fn lemma_prefix_secure_helper(&self, s1: Seq<u8>, s2: Seq<u8>, n: usize)
        requires
            s1.len() + s2.len() <= usize::MAX,
            C::is_prefix_secure(),
        ensures
            self.spec_parse_helper(s1, n).is_ok() ==> self.spec_parse_helper(s1.add(s2), n)
                == self.spec_parse_helper(s1, n),
        decreases n,
    {
        if n == 0 {
        } else {
            self.lemma_prefix_secure_helper(s1, s2, (n - 1) as usize);
            self.lemma_parse_length_helper(s1, (n - 1) as usize);
            self.lemma_parse_length_helper(s1.add(s2), (n - 1) as usize);
            if let Ok((m1, vs1)) = self.spec_parse_helper(s1, (n - 1) as usize) {
                self.0.lemma_prefix_secure(s1.skip(m1 as int), s2);
                if let Ok((m2, vs2)) = self.spec_parse_helper(s1.add(s2), (n - 1) as usize) {
                    assert(s1.skip(m1 as int).add(s2) == s1.add(s2).skip(m2 as int));
                }
            }
        }
    }

    proof fn lemma_parse_length_helper(&self, s: Seq<u8>, n: usize)
        ensures
            self.spec_parse_helper(s, n) matches Ok((m, _)) ==> m <= s.len(),
        decreases n,
    {
        if n == 0 {
        } else {
            self.lemma_parse_length_helper(s, (n - 1) as usize);
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Ok((m, vs)) => {
                    self.0.lemma_parse_length(s.skip(m as int));
                },
                Err(..) => {},
            }
        }
    }

    proof fn lemma_parse_productive_helper(&self, s: Seq<u8>, n: usize)
        requires
            self.1 > 0,
            self.0.is_productive(),
        ensures
            n > 0 ==> (self.spec_parse_helper(s, n) matches Ok((consumed, _)) ==> consumed > 0),
        decreases n,
    {
        if n == 0 {
        } else {
            self.lemma_parse_productive_helper(s, (n - 1) as usize);
            match self.spec_parse_helper(s, (n - 1) as usize) {
                Ok((m, vs)) => {
                    self.0.lemma_parse_productive(s.skip(m as int));
                },
                Err(..) => {},
            }
        }
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for RepeatN<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()> {
        self.spec_parse_helper(s, self.1)
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()> {
        self.spec_serialize_helper(v, self.1)
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for RepeatN<C> {
    open spec fn is_prefix_secure() -> bool {
        C::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        self.1 > 0 && self.0.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        self.theorem_serialize_parse_roundtrip_helper(v, self.1)
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        self.theorem_parse_serialize_roundtrip_helper(buf, self.1)
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if C::is_prefix_secure() {
            self.lemma_prefix_secure_helper(s1, s2, self.1)
        }
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        self.lemma_parse_length_helper(s, self.1)
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        self.lemma_parse_productive_helper(s, self.1)
    }
}

impl<C: SecureSpecCombinator> RepeatN<C> {
    spec fn parse_correct(
        &self,
        s: Seq<u8>,
        n: usize,
        res: Result<(usize, Seq<C::Type>), ParseError>,
    ) -> bool {
        &&& res matches Ok((k, v)) ==> {
            &&& self.spec_parse_helper(s, n) is Ok
            &&& self.spec_parse_helper(s, n) matches Ok((m, w)) ==> k == m && v == w && k <= s.len()
        }
        &&& res is Err ==> self.spec_parse_helper(s, n) is Err
        &&& self.spec_parse_helper(s, n) matches Ok((m, w)) ==> {
            &&& res is Ok
            &&& res matches Ok((k, v)) ==> m == k && w == v
        }
        &&& self.spec_parse_helper(s, n) is Err ==> res is Err
    }

    spec fn serialize_correct(
        &self,
        v: Seq<C::Type>,
        n: usize,
        data: Seq<u8>,
        old_data: Seq<u8>,
        pos: usize,
        res: Result<usize, SerializeError>,
    ) -> bool {
        &&& data.len() == old_data.len()
        &&& res matches Ok(m) ==> {
            &&& self.spec_serialize_helper(v, n) is Ok
            &&& self.spec_serialize_helper(v, n) matches Ok(b) ==> {
                m == b.len() && data == seq_splice(old_data, pos, b)
            }
        }
    }
}

impl<I, O, C> Combinator<I, O> for RepeatN<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<I, O>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
 {
    type Type = RepeatResult<C::Type>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        self.0.parse_requires() && C::V::is_prefix_secure()
    }

    fn parse(&self, input: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (mut s, mut m, mut vs) = (input, 0usize, Vec::new());
        let mut i = 0usize;
        assert(RepeatResult(vs)@ =~= seq![]);

        while i < self.1
            invariant
                0 <= i <= self.1,
                self.0.parse_requires(),
                s@ =~= input@.skip(m as int),  // <-- this is the key
                self@.parse_correct(input@, i, Ok::<_, ParseError>((m, RepeatResult(vs)@))),
        {
            i += 1;
            match self.0.parse(s.clone()) {
                Ok((n, v)) => {
                    if let Some(m_plus_n) = m.checked_add(n) {
                        let ghost old_vs = RepeatResult(vs)@;
                        vs.push(v);
                        m = m_plus_n;
                        s = s.subrange(n, s.len());
                        assert(RepeatResult(vs)@ == old_vs.push(v@));
                    } else {
                        proof {
                            self@.lemma_spec_parse_err_unrecoverable(input@, i, self.1);
                        }
                        return Err(ParseError::SizeOverflow);
                    }
                },
                Err(e) => {
                    proof {
                        self@.lemma_spec_parse_err_unrecoverable(input@, i, self.1);
                    }
                    return Err(e);
                },
            }
        }

        Ok((m, RepeatResult(vs)))
    }

    open spec fn serialize_requires(&self) -> bool {
        self.0.serialize_requires() && C::V::is_prefix_secure()
    }

    fn serialize(&self, mut vs: Self::Type, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let mut len = 0usize;
        let mut i = 0usize;

        if vs.0.len() != self.1 {
            return Err(SerializeError::RepeatNMalformed);
        }
        if pos > data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }
        let ghost old_data = data@;
        let ghost old_vs = vs@;
        assert(data@ == seq_splice(old_data, pos, seq![]));

        while i < self.1
            invariant
                0 <= i <= self.1,
                old_vs.len() == self.1,
                old_vs.take(i as int) + vs@ == old_vs,
                data@.len() == old(data)@.len(),
                self.0.serialize_requires(),
                self@.serialize_correct(
                    old_vs.take(i as int),
                    i,
                    data@,
                    old_data,
                    pos,
                    Ok::<_, SerializeError>(len),
                ),
        {
            if pos > usize::MAX - len || pos + len > data.len() {
                return Err(SerializeError::InsufficientBuffer);
            }
            match self.0.serialize(vs.0.remove(0), data, pos + len) {
                Ok(n) => {
                    if let Some(next_len) = len.checked_add(n) {
                        len = next_len;
                        i += 1;
                        assert(old_vs.take(i as int) + vs@ == old_vs);  // <-- important
                        assert(old_vs.take(i as int).drop_last() == old_vs.take((i - 1) as int));  // <-- key
                        let ghost spec_res = self@.spec_serialize_helper(old_vs.take(i as int), i);
                        assert(data@ == seq_splice(old_data, pos, spec_res.unwrap()));
                    } else {
                        return Err(SerializeError::SizeOverflow);
                    }
                },
                Err(e) => return Err(e),
            }
        }

        Ok(len)
    }
}

} // verus!
