use super::*;
use vstd::prelude::*;

verus! {

/// Essentially doing OrdChoice((C1, C2), C2),
/// but the result is mapped through
///   Left((A, B)) <-> (Some(A), B)
///   Right(B) <-> (None, B)
///
/// NOTE: we are not directly using OrdChoice since we don't want
/// to enforce C2::is_prefix_secure()
#[derive(Debug, View)]
pub struct Optional<C1, C2>(pub C1, pub C2);

pub type OptionalValue<T1, T2> = (OptionDeep<T1>, T2);

impl<C1, C2> SpecCombinator for Optional<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>,
{
    type Type = (OptionDeep<C1::Type>, C2::Type);

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            (OptionDeep::Some(v1), v2) => self.0.wf(v1) && self.1.wf(v2),
            (OptionDeep::None, v2) => self.1.wf(v2),
        }
    }
    
    open spec fn requires(&self) -> bool {
        C1::is_prefix_secure()
            && self.0.requires()
            && self.1.requires()
            && self.1.disjoint_from(&self.0)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    {
        if self.1.disjoint_from(&self.0) {
            if let Some((n, (v1, v2))) = (self.0, self.1).spec_parse(s) {
                Some((n, (OptionDeep::Some(v1), v2)))
            } else if let Some((n, v)) = self.1.spec_parse(s) {
                Some((n, (OptionDeep::None, v)))
            } else {
                None
            }
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    {
        if self.1.disjoint_from(&self.0) {
            match v {
                (OptionDeep::Some(v1), v2) => (self.0, self.1).spec_serialize((v1, v2)),
                (OptionDeep::None, v2) => self.1.spec_serialize(v2),
            }
        } else {
            seq![]
        }
    }
}

impl<C1, C2> SecureSpecCombinator for Optional<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>
{
    open spec fn is_prefix_secure() -> bool {
        C1::is_prefix_secure() && C2::is_prefix_secure()
    }
    
    open spec fn is_productive(&self) -> bool {
        self.0.is_productive() && self.1.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if self.requires() {
            assert(self.0.requires());
            assert(self.1.requires());
            assert(self.1.disjoint_from(&self.0));
            assert(C1::is_prefix_secure());
            match v {
                (OptionDeep::Some(v1), v2) => {
                    (self.0, self.1).theorem_serialize_parse_roundtrip((v1, v2));
                },
                (OptionDeep::None, v2) => {
                    let buf = self.1.spec_serialize(v2);
                    self.1.parse_disjoint_on(&self.0, buf);
                    self.1.theorem_serialize_parse_roundtrip(v2);
                },
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if self.requires() {
            assert(self.0.requires());
            assert(self.1.requires());
            assert(self.1.disjoint_from(&self.0));
            assert(C1::is_prefix_secure());
            (self.0, self.1).theorem_parse_serialize_roundtrip(buf);
            self.1.theorem_parse_serialize_roundtrip(buf);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.requires() {
            assert(self.0.requires());
            assert(self.1.requires());
            assert(self.1.disjoint_from(&self.0));
            assert(C1::is_prefix_secure());
            self.1.parse_disjoint_on(&self.0, s1.add(s2));
            (self.0, self.1).lemma_prefix_secure(s1, s2);
            self.1.lemma_prefix_secure(s1, s2);
        }
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        if self.requires() {
            assert(self.0.requires());
            assert(self.1.requires());
            assert(self.1.disjoint_from(&self.0));
            assert(C1::is_prefix_secure());
            if let Some((_, (OptionDeep::Some(_), _))) = self.spec_parse(s) {
                (self.0, self.1).lemma_parse_length(s);
            } else if let Some((_, (OptionDeep::None, _))) = self.spec_parse(s) {
                self.1.lemma_parse_length(s);
            }
        }
    }
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        if self.requires() {
            assert(self.0.requires());
            assert(self.1.requires());
            assert(self.1.disjoint_from(&self.0));
            assert(C1::is_prefix_secure());
            if let Some((_, (OptionDeep::Some(_), _))) = self.spec_parse(s) {
                (self.0, self.1).lemma_parse_productive(s);
            } else if let Some((_, (OptionDeep::None, _))) = self.spec_parse(s) {
                self.1.lemma_parse_productive(s);
            }
        }
    }
}

impl<'a, C1, C2> Combinator<'a, &'a [u8], Vec<u8>> for Optional<C1, C2> where
    C1: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    C2: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C1 as View>::V: SecureSpecCombinator<Type = <<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V>,
    <C2 as View>::V: SecureSpecCombinator<Type = <<C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V>
        + DisjointFrom<<C1 as View>::V>,
{
    type Type = OptionalValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;
    type SType = OptionalValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::SType>;

    fn length(&self, v: Self::SType) -> usize {
        match v {
            (OptionDeep::Some(v1), v2) => self.0.length(v1) + self.1.length(v2),
            (OptionDeep::None, v2) => self.1.length(v2),
        }
    }

    open spec fn ex_requires(&self) -> bool {
        self.0.ex_requires() && self.1.ex_requires()
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let pair_res = (&self.0, &self.1).parse(s);

        match pair_res {
            Ok((n, (v1, v2))) => {
                proof {
                    assert(self@.requires());
                    assert(self.1@.disjoint_from(&self.0@));

                    let pair_view = (&self.0, &self.1)@;
                    assert(pair_view.spec_parse(s@) == Some((n as int, (v1@, v2@))));

                    let opt_spec = self@.spec_parse(s@);
                    assert(opt_spec == Some((n as int, (OptionDeep::Some(v1@), v2@)))) by {
                        assert(self.1@.disjoint_from(&self.0@));
                        assert(pair_view.spec_parse(s@) == Some((n as int, (v1@, v2@))));
                    };

                    pair_view.lemma_parse_length(s@);
                }

                Ok((n, (OptionDeep::Some(v1), v2)))
            }
            Err(_) => {
                match self.1.parse(s) {
                    Ok((n, v2)) => {
                        proof {
                            assert(self@.requires());
                            assert(self.1@.disjoint_from(&self.0@));

                            let pair_view = (&self.0, &self.1)@;
                            assert(pair_view.spec_parse(s@).is_none());

                            let c2_spec = self.1@.spec_parse(s@);
                            assert(c2_spec == Some((n as int, v2@)));

                            let opt_spec = self@.spec_parse(s@);
                            assert(opt_spec == Some((n as int, (OptionDeep::<
                                <<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View
                            >::V>::None, v2@)))) by {
                                assert(self.1@.disjoint_from(&self.0@));
                                assert(pair_view.spec_parse(s@).is_none());
                                assert(c2_spec == Some((n as int, v2@)));
                            };

                            self.1@.lemma_parse_length(s@);
                        }

                        Ok((n, (OptionDeep::None, v2)))
                    }
                    Err(e) => {
                        proof {
                            assert(self@.requires());
                            assert(self.1@.disjoint_from(&self.0@));

                            let pair_view = (&self.0, &self.1)@;
                            assert(pair_view.spec_parse(s@).is_none());
                            let c2_spec = self.1@.spec_parse(s@);
                            assert(c2_spec.is_none());
                            assert(self@.spec_parse(s@).is_none());
                        }

                        Err(e)
                    }
                }
            }
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let len = match v {
            (OptionDeep::Some(v1), v2) => (&self.0, &self.1).serialize((v1, v2), data, pos),
            (OptionDeep::None, v2) => self.1.serialize(v2, data, pos),
        }?;

        proof {
            assert(self@.requires());
        }

    assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@)));

        Ok(len)
    }
}

/// If T2 and T3 are both disjoint from T1, then
/// something like Optional<T1, Optional<T2, T3>> is doable
impl<T1, T2, T3> DisjointFrom<T1> for Optional<T2, T3> where
    T1: SecureSpecCombinator,
    T2: SecureSpecCombinator,
    T3: SecureSpecCombinator,
    T2: DisjointFrom<T1>,
    T3: DisjointFrom<T1>,
    T3: DisjointFrom<T2>,
{
    open spec fn disjoint_from(&self, other: &T1) -> bool {
        self.0.disjoint_from(other) &&
        self.1.disjoint_from(other)
    }

    proof fn parse_disjoint_on(&self, other: &T1, buf: Seq<u8>) {
        self.0.parse_disjoint_on(other, buf);
        self.1.parse_disjoint_on(other, buf);
    }
}

}
