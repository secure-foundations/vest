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

pub type DefaultValue<T1, T2> = (T1, T2);

impl<C1, C2> SpecCombinator for Default<C1::Type, C1, C2> where
    C1: SecureSpecCombinator,
    C2: SecureSpecCombinator + DisjointFrom<C1>,
{
    type Type = (C1::Type, C2::Type);

    open spec fn wf(&self, v: Self::Type) -> bool {
        match v {
            (v1, v2) => 
            {
                &&& self.0 != v1 ==> (self.1, self.2).wf((v1, v2))
                &&& self.0 == v1 ==> self.2.wf(v2)
            }
        }
    }
    
    open spec fn requires(&self) -> bool {
        &&& (self.1, self.2).requires()
        &&& self.2.requires()
        &&& self.2.disjoint_from(&self.1)
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)>
    {
        if let Some((n, (v1, v2))) = (self.1, self.2).spec_parse(s) {
            if v1 != self.0 {
                Some((n, (v1, v2)))
            } else {
                None
            }
        } else if let Some((n, v)) = self.2.spec_parse(s) {
            Some((n, (self.0, v)))
        } else {
            None
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8>
    {
        if self.0 == v.0 {
            self.2.spec_serialize(v.1)
        } else {
            (self.1, self.2).spec_serialize((v.0, v.1))
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
    
    open spec fn is_productive(&self) -> bool {
        self.1.is_productive() && self.2.is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        if self.0 == v.0 {
            let (buf) = self.2.spec_serialize(v.1);
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
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        (self.1, self.2).lemma_parse_length(s);
        self.2.lemma_parse_length(s);
    }
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        (self.1, self.2).lemma_parse_productive(s);
        self.2.lemma_parse_productive(s);
    }
}

impl<'a, C1, C2> Combinator<'a, &'a [u8], Vec<u8>> for Default<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType, C1, C2> where
    C1: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    C2: for<'x> Combinator<'x, &'x [u8], Vec<u8>>,
    <C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType: PolyfillClone + PolyfillEq,
    <C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type: PolyfillEq + From<<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::SType>,
    <C1 as View>::V: SecureSpecCombinator<
        Type = <<C1 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V
    >,
    <C2 as View>::V: SecureSpecCombinator<
        Type = <<C2 as Combinator<'a, &'a [u8], Vec<u8>>>::Type as View>::V
    > + DisjointFrom<<C1 as View>::V>,
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

    open spec fn ex_requires(&self) -> bool {
        self.1.ex_requires() && self.2.ex_requires()
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let pair = (&self.1, &self.2);
        let res = if let Ok((n, (v1, v2))) = pair.parse(s) {
            if !v1.polyfill_eq(&self.0.clone().ex_into()) {
                Ok((n, (v1, v2)))
            } else {
                Err(ParseError::Other("Default value should be omitted".to_string()))
            }
        } else if let Ok((n, v2)) = self.2.parse(s) {
            Ok((n, (self.0.clone().ex_into(), v2)))
        } else {
            Err(ParseError::OrdChoiceNoMatch)
        };

        res
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let pair = (&self.1, &self.2);
        let len = if v.0.polyfill_eq(&self.0.clone().ex_into()) {
            self.2.serialize(v.1, data, pos)?
        } else {
            pair.serialize((v.0, v.1), data, pos)?
        };

        assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(v@)));

        Ok(len)
    }
}

impl<T1, T2, T3> DisjointFrom<T1> for Default<T2::Type, T2, T3> where
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
