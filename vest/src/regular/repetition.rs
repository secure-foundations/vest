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
            &&& self.spec_serialize_helper(v, n) matches Ok(b)
            &&& b.len() == m
            &&& data == seq_splice(old_data, pos, b)
        }
        // res matches Ok(m) ==> {
        //     &&& self.spec_serialize_helper(v, n) is Ok
        //     &&& self.spec_serialize_helper(v, n) matches Ok(b) ==> {
        //         m == b.len() && data == seq_splice(old_data, pos, b)
        //     }
        // }
    }
}

impl<I, O, C, 'x> Combinator<'x, I, O> for RepeatN<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O, SType = &'x <C as Combinator<'x, I, O>>::Type>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    <C as Combinator<'x, I, O>>::Type: 'x
 {
    type Type = RepeatResult<C::Type>;

    type SType = &'x RepeatResult<C::Type>;

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
            decreases self.1 - i,
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

    #[verifier::external_body]
    fn serialize(&self, vs: Self::SType, data: &mut O, pos: usize) -> (res: Result<
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
                vs@.len() == self.1,
                data@.len() == old(data)@.len(),
                self.0.serialize_requires(),
                self@.serialize_correct(
                    vs@.take(i as int),
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
            match self.0.serialize(&vs.0[i], data, pos + len) {
                // match self.0.serialize(vs.0.remove(0), data, pos + len) {
                Ok(n) => {
                    if let Some(next_len) = len.checked_add(n) {
                        len = next_len;
                        i += 1;
                        assert(vs@.take(i as int).drop_last() == vs@.take((i - 1) as int));  // <-- key
                        let ghost spec_bytes = self@.spec_serialize_helper(vs@.take(i as int), i);
                        assert(data@ == seq_splice(old_data, pos, spec_bytes.unwrap()));
                    } else {
                        return Err(SerializeError::SizeOverflow);
                    }
                },
                Err(e) => return Err(e),
            }
        }

        assert(vs@.take(i as int) =~= vs@);
        Ok(len)
    }
}

/// A combinator to repeatedly parse/serialize the inner combinator C
/// until the end of the buffer.
///
/// If the inner combinator fails before the end of the buffer, Repeat fails
pub struct Repeat<C>(pub C);

/// Wrappers around Vec so that their View's can be implemented as DeepView
#[derive(Debug, PartialEq, Eq)]
pub struct RepeatResult<T>(pub Vec<T>);

impl<T: Clone> Clone for RepeatResult<T> {
    fn clone(&self) -> Self {
        RepeatResult(self.0.clone())
    }
}

impl<'x, C: View> Repeat<C> where
    C::V: SecureSpecCombinator,
 {
    /// Constructs a new `Repeat` combinator, only if the inner combinator is productive.
    pub fn new(c: C) -> (o: Self)
        requires
            c@.is_productive(),
        ensures
            o == Self(c),
    {
        Repeat(c)
    }
}

impl<C: View> View for Repeat<C> {
    type V = Repeat<<C as View>::V>;

    open spec fn view(&self) -> Self::V {
        Repeat(self.0@)
    }
}

impl<T: View> View for RepeatResult<T> {
    type V = Seq<T::V>;

    open spec fn view(&self) -> Self::V {
        Seq::new(self.0.len() as nat, |i: int| self.0@[i]@)
    }
}

impl<C: SecureSpecCombinator> SpecCombinator for Repeat<C> {
    type Type = Seq<C::Type>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
        decreases s.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if s.len() == 0 {
            Ok((0, seq![]))
        } else {
            match self.0.spec_parse(s) {
                Ok((n, v)) => if 0 < n <= s.len() {
                    match self.spec_parse(s.skip(n as int)) {
                        Ok((_, vs)) => Ok((s.len() as usize, seq![v] + vs)),
                        Err(..) => Err(()),
                    }
                } else {
                    Err(())
                },
                Err(..) => Err(()),
            }
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
        decreases v.len(),
    {
        if !C::is_prefix_secure() {
            Err(())
        } else if v.len() == 0 {
            Ok(seq![])
        } else {
            match self.0.spec_serialize(v[0]) {
                Ok(s) => if s.len() != 0 {
                    match self.spec_serialize(v.drop_first()) {
                        Ok(rest) => if s.len() + rest.len() <= usize::MAX {
                            Ok(s + rest)
                        } else {
                            Err(())
                        },
                        Err(..) => Err(()),
                    }
                } else {
                    Err(())
                },
                Err(..) => Err(()),
            }
        }
    }
}

impl<C: SecureSpecCombinator> SecureSpecCombinator for Repeat<C> {
    /// Prepending bytes to the buffer may result in more items parsed
    /// so Repeat is not prefix secure
    open spec fn is_prefix_secure() -> bool {
        false
    }

    open spec fn is_productive(&self) -> bool {
        false
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v.len(),
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
                if C::is_prefix_secure() && s.len() + rest.len() <= usize::MAX {
                    self.0.lemma_prefix_secure(s, rest);
                    let (n, _) = self.0.spec_parse(s + rest).unwrap();
                    self.0.lemma_parse_length(s + rest);

                    assert((s + rest).skip(n as int) =~= rest);
                    assert(seq![v[0]] + v.drop_first() == v);
                }
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
        decreases buf.len(),
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

                if C::is_prefix_secure() {
                    assert(v2 == v.drop_first());
                    assert(buf.subrange(0, n1 as int) + buf.skip(n1 as int).subrange(0, n2 as int)
                        == buf.subrange(0, n as int));
                }
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
    }
}

impl<I, O, C, 'x> Combinator<'x, I, O> for Repeat<C> where
    I: VestInput,
    O: VestOutput<I>,
    C: Combinator<'x, I, O, SType = &'x <C as Combinator<'x, I, O>>::Type>,
    C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
    <C as Combinator<'x, I, O>>::Type: 'x
 {
    type Type = RepeatResult<C::Type>;

    type SType = &'x RepeatResult<C::Type>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.parse_requires()
        &&& self.0@.is_productive()
    }

    fn parse(&self, s: I) -> (res: Result<(usize, Self::Type), ParseError>) {
        let mut res = Vec::new();
        let mut offset: usize = 0;

        assert(s@.subrange(0, s@.len() as int) == s@);

        while offset < s.len()
            invariant
                0 <= offset <= s@.len(),
                self.parse_requires(),
                self@.spec_parse(s@.subrange(offset as int, s@.len() as int)) matches Ok((_, rest))
                    ==> {
                    &&& self@.spec_parse(s@) matches Ok((_, v))
                    &&& RepeatResult(res)@ + rest =~= v
                },
                offset < s@.len() ==> (self@.spec_parse(
                    s@.subrange(offset as int, s@.len() as int),
                ) is Err ==> self@.spec_parse(s@) is Err),
            decreases s@.len() - offset,
        {
            let (n, v) = self.0.parse(s.subrange(offset, s.len()))?;
            assert(n > 0) by {
                self.0@.lemma_parse_productive(s@.subrange(offset as int, s@.len() as int));
            }

            let ghost prev_offset = offset;

            res.push(v);
            offset += n;

            assert(s@.subrange(prev_offset as int, s@.len() as int).skip(n as int) =~= s@.subrange(
                offset as int,
                s@.len() as int,
            ))
        }

        let ghost empty: Seq<u8> = seq![];
        assert(s@.subrange(s@.len() as int, s@.len() as int) == empty);

        Ok(
            (s.len(), RepeatResult(res)),
        )
        // self.parse_helper(s.clone(), &mut res)?;
        // Ok((s.len(), RepeatResult(res)))

    }

    open spec fn serialize_requires(&self) -> bool {
        &&& <C as View>::V::is_prefix_secure()
        &&& self.0.serialize_requires()
        &&& self.0@.is_productive()
    }

    #[verifier::external_body]
    fn serialize(&self, mut vs: Self::SType, data: &mut O, pos: usize) -> (res: Result<
        usize,
        SerializeError,
    >) {
        let mut len = 0usize;
        let mut i = 0usize;
        let cnt = vs.0.len();

        if pos > data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }
        let ghost old_data = data@;
        let ghost old_vs = vs@;
        assert(data@ == seq_splice(old_data, pos, seq![]));

        while i < cnt
            invariant
                0 <= i <= cnt,
                vs@.len() == cnt,
                data@.len() == old(data)@.len(),
                self.serialize_requires(),
                self@.spec_serialize(vs@) matches Ok(b) && b.len() == len && data@ == seq_splice(
                    old_data,
                    pos,
                    b,
                ),
        // res matches Ok(n) ==> {
        //     &&& self@.spec_serialize(v@) matches Ok(b)
        //     &&& b.len() == n
        //     &&& buf@ == seq_splice(old(buf)@, pos, b)
        // },
        // self@.serialize_correct(
        //     vs@.take(i as int),
        //     i,
        //     data@,
        //     old_data,
        //     pos,
        //     Ok::<_, SerializeError>(len),
        // ),
        {
            if pos > usize::MAX - len || pos + len > data.len() {
                return Err(SerializeError::InsufficientBuffer);
            }
            match self.0.serialize(&vs.0[i], data, pos + len) {
                // match self.0.serialize(vs.0.remove(0), data, pos + len) {
                Ok(n) => {
                    assert(n > 0) by {
                        self.0@.lemma_serialize_productive(vs@[i as int]);
                    }
                    if let Some(next_len) = len.checked_add(n) {
                        len = next_len;
                        i += 1;
                        assert(vs@.take(i as int).drop_last() == vs@.take((i - 1) as int));  // <-- key
                        let ghost spec_bytes = self@.spec_serialize(vs@.take(i as int));
                        assert(data@ == seq_splice(old_data, pos, spec_bytes.unwrap()));
                    } else {
                        return Err(SerializeError::SizeOverflow);
                    }
                },
                Err(e) => return Err(e),
            }
        }

        assert(vs@.take(i as int) =~= vs@);
        Ok(len)
    }
}


// /// A combinator to parse/serialize the inner combinator C
// /// zero or more times until the end of the buffer.
// ///
// /// If the inner combinator fails before the end of the buffer,
// /// `Star` will return the parsed items so far.
// pub struct Star<C>(pub C);

// impl<C: View> View for Star<C> {
//     type V = Star<<C as View>::V>;

//     open spec fn view(&self) -> Self::V {
//         Star(self.0@)
//     }
// }

// impl<C: SecureSpecCombinator> Star<C> {
//     /// Helper function for spec_parse()
//     pub closed spec fn spec_parse_helper(
//         &self,
//         s: Seq<u8>,
//         res: Seq<C::Type>,
//         consumed: usize,
//         len: usize,
//     ) -> Result<(usize, Seq<C::Type>), ()>
//         decreases s.len(),
//     {
//         match self.0.spec_parse(s) {
//             Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
//                 self.spec_parse_helper(s.skip(n as int), res.push(v), (consumed + n) as usize, len)
//             } else {
//                 Err(())
//             },
//             Err(..) => Ok((consumed, res)),
//         }
//     }

//     pub closed spec fn spec_serialize_helper(&self, v: Seq<C::Type>, res: Seq<u8>) -> Result<
//         Seq<u8>,
//         (),
//     >
//         decreases v.len(),
//     {
//         if v.len() == 0 {
//             Ok(res)
//         } else {
//             match self.0.spec_serialize(v[0]) {
//                 Ok(s) => if s.len() != 0 {
//                     self.spec_serialize_helper(v.drop_first(), res + s)
//                 } else {
//                     Err(())
//                 },
//                 Err(..) => Err(()),
//             }
//         }
//     }
// }

// impl<C: SecureSpecCombinator> Star<C> {
//     proof fn theorem_parse_serialize_roundtrip_helper(
//         &self,
//         s: Seq<u8>,
//         vs: Seq<C::Type>,
//         consumed: usize,
//         len: usize,
//     )
//         requires
//             C::is_prefix_secure(),
//             s.len() <= usize::MAX,
//             consumed <= len,
//             self.spec_serialize(vs) == Ok::<_, ()>(s.take(consumed as int)),
//         ensures
//             self.spec_parse_helper(s, vs, consumed, len) matches Ok((consumed, v))
//                 ==> self.spec_serialize(v) == Ok::<_, ()>(s.take(consumed as int)),
//         decreases s.len(),
//     {
//         self.lemma_parse_length_helper(s, vs, consumed, len);
//         match self.0.spec_parse(s) {
//             Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
//                 self.0.theorem_parse_serialize_roundtrip(s);
//                 assert(self.0.spec_serialize(v) == Ok::<_, ()>(s.take(n as int)));
//                 admit();
//                 assume(self.spec_serialize(vs.push(v)) == Ok::<_, ()>(
//                     s.skip(n as int).take(consumed + n as int),
//                 ));
//                 self.theorem_parse_serialize_roundtrip_helper(
//                     s.skip(n as int),
//                     vs.push(v),
//                     (consumed + n) as usize,
//                     len,
//                 );

//             } else {
//             },
//             Err(..) => {},
//         }

//     }

//     proof fn lemma_parse_length_helper(
//         &self,
//         s: Seq<u8>,
//         res: Seq<C::Type>,
//         consumed: usize,
//         len: usize,
//     )
//         requires
//             consumed <= len,
//         ensures
//             self.spec_parse_helper(s, res, consumed, len) matches Ok((m, _)) ==> m <= len,
//         decreases s.len(),
//     {
//         match self.0.spec_parse(s) {
//             Ok((n, v)) => if 0 < n <= s.len() && consumed + n <= len {
//                 self.lemma_parse_length_helper(
//                     s.skip(n as int),
//                     res.push(v),
//                     (consumed + n) as usize,
//                     len,
//                 )
//             } else {
//             },
//             Err(..) => {},
//         }
//     }
// }

// impl<C: SecureSpecCombinator> SpecCombinator for Star<C> {
//     type Type = Seq<C::Type>;

//     open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
//         decreases s.len(),
//     {
//         if !C::is_prefix_secure() {
//             Err(())
//         } else {
//             self.spec_parse_helper(s, seq![], 0, s.len() as usize)
//         }
//     }

//     open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
//         decreases v.len(),
//     {
//         if !C::is_prefix_secure() {
//             Err(())
//         } else {
//             self.spec_serialize_helper(v, seq![])
//         }
//     }
// }

// impl<C: SecureSpecCombinator> SecureSpecCombinator for Star<C> {
//     /// Prepending bytes to the buffer may result in more items parsed
//     /// so Star is not prefix secure
//     open spec fn is_prefix_secure() -> bool {
//         false
//     }

//     open spec fn is_productive(&self) -> bool {
//         false
//     }

//     proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
//         decreases v.len(),
//     {
//         admit();
//     }

//     proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>)
//         decreases buf.len(),
//     {
//         if C::is_prefix_secure() {
//             assert(Seq::<u8>::empty() == buf.take(0));
//             self.theorem_parse_serialize_roundtrip_helper(buf, seq![], 0, buf.len() as usize);
//         }
//     }

//     proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
//     }

//     proof fn lemma_parse_length(&self, s: Seq<u8>) {
//         self.lemma_parse_length_helper(s, seq![], 0, s.len() as usize);
//     }

//     proof fn lemma_parse_productive(&self, s: Seq<u8>) {
//     }
// }

// impl<I, O, C> Combinator<I, O> for Star<C> where
//     I: VestInput,
//     O: VestOutput<I>,
//     C: Combinator<I, O>,
//     C::V: SecureSpecCombinator<Type = <C::Type as View>::V>,
//  {
//     type Type = RepeatResult<C::Type>;

//     open spec fn spec_length(&self) -> Option<usize> {
//         None
//     }

//     fn length(&self) -> Option<usize> {
//         None
//     }

//     open spec fn parse_requires(&self) -> bool {
//         self.0.parse_requires() && C::V::is_prefix_secure()
//     }

//     #[verifier::external_body]
//     fn parse(&self, mut input: I) -> (res: Result<(usize, Self::Type), ParseError>) {
//         let mut res = Vec::new();
//         let mut consumed: usize = 0;
//         loop {
//             match self.0.parse(input.clone()) {
//                 Ok((n, v)) => {
//                     // check for infinite loop
//                     if n > 0 {
//                         if let Some(next_consumed) = consumed.checked_add(n) {
//                             consumed = next_consumed;
//                         } else {
//                             return Err(ParseError::SizeOverflow);
//                         }
//                         res.push(v);
//                         input = input.subrange(n, input.len());
//                     } else {
//                         return Err(ParseError::RepeatEmptyElement);
//                     }
//                 },
//                 Err(..) => return Ok((consumed, RepeatResult(res))),
//             }
//         }
//     }

//     open spec fn serialize_requires(&self) -> bool {
//         self.0.serialize_requires() && C::V::is_prefix_secure()
//     }

//     #[verifier::external_body]
//     fn serialize(&self, mut vs: Self::Type, data: &mut O, pos: usize) -> (res: Result<
//         usize,
//         SerializeError,
//     >) {
//         let mut len: usize = 0;
//         loop {
//             if vs.0.len() == 0 {
//                 return Ok(len);
//             }
//             if pos > usize::MAX - len || pos + len > data.len() {
//                 return Err(SerializeError::InsufficientBuffer);
//             }
//             match self.0.serialize(vs.0.remove(0), data, pos + len) {
//                 Ok(n) => {
//                     if let Some(next_len) = len.checked_add(n) {
//                         len = next_len;
//                     } else {
//                         return Err(SerializeError::SizeOverflow);
//                     }
//                     if n == 0 {
//                         return Err(SerializeError::RepeatEmptyElement);
//                     }
//                 },
//                 Err(e) => return Err(e),
//             }
//         }
//     }
// }

} // verus!
