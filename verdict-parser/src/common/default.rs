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

impl<C1, C2> SpecCombinator for Default<C1::Type, C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>,
{
    type Type = PairValue<C1::Type, C2::Type>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        true
    }
    
    open spec fn requires(&self) -> bool {
        true
    }

    spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    {
        if self.2.disjoint_from(&self.1) {
            if let Some((n, (v1, v2))) = (self.1, self.2).spec_parse(s) {
                if v1 != self.0 {
                    Some((n, PairValue(v1, v2)))
                } else {
                    None
                }
            } else if let Some((n, v)) = self.2.spec_parse(s) {
                Some((n, PairValue(self.0, v)))
            } else {
                None
            }
        } else {
            None
        }
    }

    spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    {
        if self.2.disjoint_from(&self.1) {
            if self.0 == v.0 {
                self.2.spec_serialize(v.1)
            } else {
                (self.1, self.2).spec_serialize((v.0, v.1))
            }
        } else {
            seq![]
        }
    }
}

impl<C1, C2> SecureSpecCombinator for Default<C1::Type, C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>
{
    open spec fn is_prefix_secure() -> bool {
        C1::is_prefix_secure() && C2::is_prefix_secure()
    }
    
    spec fn is_productive() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if self.0 == v.0 {
            let buf = self.2.spec_serialize(v.1);
            if self.2.disjoint_from(&self.1) {
                self.2.parse_disjoint_on(&self.1, buf);
            }

            self.2.theorem_serialize_parse_roundtrip(v.1)
        } else {
            (self.1, self.2).theorem_serialize_parse_roundtrip((v.0, v.1))
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        (self.1, self.2).theorem_parse_serialize_roundtrip(buf);
        self.2.theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        if self.2.disjoint_from(&self.1) {
            self.2.parse_disjoint_on(&self.1, s1.add(s2));
            (self.1, self.2).lemma_prefix_secure(s1, s2);
            self.2.lemma_prefix_secure(s1, s2);
        }
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a, C1, C2> Combinator<'a, &'a [u8], Vec<u8>> for Default<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType, C1, C2> where
    C1: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    C2: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType: PolyfillClone,
    <C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type: PolyfillEq + From<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType>,
    <C1 as View>::V: SecureSpecCombinator,
    <C2 as View>::V: SecureSpecCombinator + DisjointFrom<<C1 as View>::V>,
{
    type Type = DefaultValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type>;
    type SType = DefaultValue<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType, <C2 as Combinator<'a, &'a [u8], Vec<u8>>>::SType>;

    fn length(&self, v: Self::SType) -> usize {
        if v.0.polyfill_eq(&self.0) {
            self.2.length(v.1)
        } else {
            self.1.length(v.0) + self.2.length(v.1)
        }
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
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

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
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
