use super::*;
use vstd::prelude::*;

verus! {

/// Default(a, C1, C2) is similar to Optional(C1, C2)
/// except that if C1 is not matched, a is used in place
/// Conversely, if C1 exists, the value cannot be a.
///
/// Used for ASN.1 default fields
#[derive(Debug, View)]
pub struct Default<T, C1, C2>(pub T, pub C1, pub C2);

pub type DefaultValue<T1, T2> = PairValue<T1, T2>;

impl<C1, C2> SpecCombinator for Default<C1::SpecResult, C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>,
{
    type SpecResult = PairValue<C1::SpecResult, C2::SpecResult>;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()>
    {
        if self.2.disjoint_from(&self.1) {
            if let Ok((n, (v1, v2))) = (self.1, self.2).spec_parse(s) {
                if v1 != self.0 {
                    Ok((n, PairValue(v1, v2)))
                } else {
                    Err(())
                }
            } else if let Ok((n, v)) = self.2.spec_parse(s) {
                Ok((n, PairValue(self.0, v)))
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        (self.1, self.2).spec_parse_wf(s);
        self.2.spec_parse_wf(s);
    }

    open spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()>
    {
        if self.2.disjoint_from(&self.1) {
            if self.0 == v.0 {
                self.2.spec_serialize(v.1)
            } else {
                (self.1, self.2).spec_serialize((v.0, v.1))
            }
        } else {
            Err(())
        }
    }
}

impl<C1, C2> SecureSpecCombinator for Default<C1::SpecResult, C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>
{
    open spec fn is_prefix_secure() -> bool {
        C1::is_prefix_secure() && C2::is_prefix_secure()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if self.0 == v.0 {
            if let Ok(buf) = self.2.spec_serialize(v.1) {
                if self.2.disjoint_from(&self.1) {
                    self.2.parse_disjoint_on(&self.1, buf);
                }
            }

            self.2.theorem_serialize_parse_roundtrip(v.1)
        } else {
            (self.1, self.2).theorem_serialize_parse_roundtrip((v.0, v.1))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (self.1, self.2).theorem_parse_serialize_roundtrip(buf);
        self.2.theorem_parse_serialize_roundtrip(buf);
        assert(self.spec_parse(buf) matches Ok((n, v)) ==> self.spec_serialize(v).unwrap() == buf.subrange(0, n as int));
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.2.disjoint_from(&self.1) {
            self.2.parse_disjoint_on(&self.1, s1.add(s2));
            (self.1, self.2).lemma_prefix_secure(s1, s2);
            self.2.lemma_prefix_secure(s1, s2);
        }
    }
}

impl<C1, C2> Combinator for Default<C1::Owned, C1, C2> where
    C1: Combinator,
    C2: Combinator,

    // Requires converting from C1::Owned to C1::Result
    C1::Owned: PolyfillClone,
    for <'a> C1::Result<'a>: PolyfillEq + From<C1::Owned>,

    C1::V: SecureSpecCombinator<SpecResult = <C1::Owned as View>::V>,
    C2::V: SecureSpecCombinator<SpecResult = <C2::Owned as View>::V> + DisjointFrom<C1::V>,
{
    type Result<'a> = DefaultValue<C1::Result<'a>, C2::Result<'a>>;
    type Owned = DefaultValue<C1::Owned, C2::Owned>;

    open spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    open spec fn parse_requires(&self) -> bool {
        &&& self.1.parse_requires()
        &&& self.2.parse_requires()
        &&& self.2@.disjoint_from(&self.1@)
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let res = if let Ok((n, (v1, v2))) = (&self.1, &self.2).parse(s) {
            if !v1.polyfill_eq(&self.0.clone().ex_into()) {
                Ok((n, PairValue(v1, v2)))
            } else {
                Err(ParseError::Other("Default value should be omitted".to_string()))
            }
        } else if let Ok((n, v2)) = self.2.parse(s) {
            Ok((n, PairValue(self.0.clone().ex_into(), v2)))
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
        &&& self.1.serialize_requires()
        &&& self.2.serialize_requires()
        &&& self.2@.disjoint_from(&self.1@)
        &&& C1::V::is_prefix_secure()
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let len = if v.0.polyfill_eq(&self.0.clone().ex_into()) {
            self.2.serialize(v.1, data, pos)?
        } else {
            (&self.1, &self.2).serialize((v.0, v.1), data, pos)?
        };

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@).unwrap()));

        Ok(len)
    }
}

impl<T1, T2, T3> DisjointFrom<T1> for Default<T2::SpecResult, T2, T3> where
    T1: SecureSpecCombinator,
    T2: SecureSpecCombinator,
    T3: SecureSpecCombinator,
    T2: DisjointFrom<T1>,
    T3: DisjointFrom<T1>,
    T3: DisjointFrom<T2>,
{
    open spec fn disjoint_from(&self, other: &T1) -> bool {
        self.1.disjoint_from(other) &&
        self.2.disjoint_from(other)
    }

    proof fn parse_disjoint_on(&self, other: &T1, buf: Seq<u8>) {
        self.1.parse_disjoint_on(other, buf);
        self.2.parse_disjoint_on(other, buf);
    }
}

}
