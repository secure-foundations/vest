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

pub type OptionalValue<T1, T2> = PairValue<OptionDeep<T1>, T2>;

impl<C1, C2> SpecCombinator for Optional<C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>,
{
    type SpecResult = PairValue<OptionDeep<C1::SpecResult>, C2::SpecResult>;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        if self.1.disjoint_from(&self.0) {
            if let Ok((n, (v1, v2))) = (self.0, self.1).spec_parse(s) {
                Ok((n, PairValue(OptionDeep::Some(v1), v2)))
            } else if let Ok((n, v)) = self.1.spec_parse(s) {
                Ok((n, PairValue(OptionDeep::None, v)))
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        (self.0, self.1).spec_parse_wf(s);
        self.1.spec_parse_wf(s);
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>
    {
        if self.1.disjoint_from(&self.0) {
            match v {
                PairValue(OptionDeep::Some(v1), v2) => (self.0, self.1).spec_serialize((v1, v2)),
                PairValue(OptionDeep::None, v2) => self.1.spec_serialize(v2),
            }
        } else {
            Err(())
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

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        match v {
            PairValue(OptionDeep::Some(v1), v2) => {
                (self.0, self.1).theorem_serialize_parse_roundtrip((v1, v2));
            },
            PairValue(OptionDeep::None, v2) => {
                if let Ok(buf) = self.1.spec_serialize(v2) {
                    if self.1.disjoint_from(&self.0) {
                        self.1.parse_disjoint_on(&self.0, buf);
                    }
                }
                self.1.theorem_serialize_parse_roundtrip(v2);
            },
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (self.0, self.1).theorem_parse_serialize_roundtrip(buf);
        self.1.theorem_parse_serialize_roundtrip(buf);
        assert(self.spec_parse(buf) matches Ok((n, v)) ==> self.spec_serialize(v).unwrap() == buf.subrange(0, n as int));
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.1.disjoint_from(&self.0) {
            self.1.parse_disjoint_on(&self.0, s1.add(s2));
            (self.0, self.1).lemma_prefix_secure(s1, s2);
            self.1.lemma_prefix_secure(s1, s2);
        }
    }
}

impl<C1, C2> Combinator for Optional<C1, C2> where
    C1: Combinator,
    C2: Combinator,

    C1::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
    C2::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V> + DisjointFrom<C1::V>,
{
    type Result<'a> = OptionalValue<C1::Result<'a>, C2::Result<'a>>;
    type Owned = OptionalValue<C1::Owned, C2::Owned>;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.0.parse_requires()
        &&& self.1.parse_requires()
        &&& self.1@.disjoint_from(&self.0@)
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let res = if let Ok((n, (v1, v2))) = (&self.0, &self.1).parse(s) {
            Ok((n, PairValue(OptionDeep::Some(v1), v2)))
        } else if let Ok((n, v2)) = self.1.parse(s) {
            Ok((n, PairValue(OptionDeep::None, v2)))
        } else {
            Err(ParseError::OrdChoiceNoMatch)
        };

        // TODO: why do we need this?
        assert(res matches Ok((n, v)) ==> {
            &&& self@.spec_parse(s@) is Ok
            &&& self@.spec_parse(s@) matches Ok((m, w)) ==> n == m && v@ == w && n <= s@.len()
        });

        res
    }

    open spec fn serialize_requires(&self) -> bool {
        &&& self.0.serialize_requires()
        &&& self.1.serialize_requires()
        &&& self.1@.disjoint_from(&self.0@)
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let len = match v {
            PairValue(OptionDeep::Some(v1), v2) => (&self.0, &self.1).serialize((v1, v2), data, pos),
            PairValue(OptionDeep::None, v2) => self.1.serialize(v2, data, pos),
        }?;

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

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
