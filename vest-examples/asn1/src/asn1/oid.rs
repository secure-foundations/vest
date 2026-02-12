use super::*;
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// Combinator for ASN.1 Object Identifier
#[derive(Debug, View)]
pub struct ObjectIdentifier;

asn1_tagged!(ObjectIdentifier, tag_of!(OBJECT_IDENTIFIER));

pub type SpecObjectIdentifierValue = Seq<UInt>;

pub type VecDeep<T> = RepeatResult<T>;
#[derive(Eq, PartialEq)]
pub struct ObjectIdentifierValue(pub VecDeep<UInt>);
pub type ObjectIdentifierValueOwned = ObjectIdentifierValue;

impl View for ObjectIdentifierValue {
    type V = Seq<UInt>;

    open spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl ObjectIdentifier {
    /// First byte of an OID is 40 * arc1 + arc2
    pub closed spec fn parse_first_two_arcs(byte: u8) -> Option<(UInt, UInt)> {
        let arc1 = byte / 40;
        let arc2 = byte % 40;

        if arc1 <= 2 && arc2 <= 39 {
            Some((arc1 as UInt, arc2 as UInt))
        } else {
            None
        }
    }

    pub closed spec fn serialize_first_two_arcs(arc1: UInt, arc2: UInt) -> Option<u8> {
        if arc1 <= 2 && arc2 <= 39 {
            Some((arc1 * 40 + arc2) as u8)
        } else {
            None
        }
    }

    proof fn lemma_serialize_parse_first_two_arcs(arc1: UInt, arc2: UInt)
        ensures
            Self::serialize_first_two_arcs(arc1, arc2) matches Some(byte) ==>
                Self::parse_first_two_arcs(byte) == Some((arc1, arc2))
    {}

    proof fn lemma_parse_serialize_first_two_arcs(byte: u8)
        ensures
            Self::parse_first_two_arcs(byte) matches Some((arc1, arc2)) ==>
                Self::serialize_first_two_arcs(arc1, arc2) == Some(byte)
    {}
}

impl SpecCombinator for ObjectIdentifier {
    type Type = SpecObjectIdentifierValue;

    open spec fn wf(&self, v: Self::Type) -> bool {
        v.len() >= 2 && v.len() <= usize::MAX &&
            (Self::serialize_first_two_arcs(v[0], v[1]) matches Some(first_byte) && ({
                    let rest_arcs = v.skip(2);
                    let buf = (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs));
                    new_spec_object_identifier_inner().wf((buf.len() as LengthValue, (first_byte, rest_arcs)))
                }))
    }
    
    open spec fn requires(&self) -> bool {
        new_spec_object_identifier_inner().requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match new_spec_object_identifier_inner().spec_parse(s) {
            Some((len, (_, (first, rest_arcs)))) =>
                match Self::parse_first_two_arcs(first) {
                    Some((arc1, arc2)) =>
                        if rest_arcs.len() + 2 <= usize::MAX {
                            Some((len, seq![ arc1, arc2 ] + rest_arcs))
                        } else {
                            None
                        }
                    None => None,
                }

            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        if v.len() < 2 || v.len() > usize::MAX {
            seq![]
        } else {
            match Self::serialize_first_two_arcs(v[0], v[1]) {
                Some(first_byte) => {
                    let rest_arcs = v.skip(2);

                    // Compute the inner length first
                    let buf = (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs));
                    new_spec_object_identifier_inner().spec_serialize((buf.len() as LengthValue, (first_byte, rest_arcs)))
                },
                None => seq![],
            }
        }
    }
}

impl SecureSpecCombinator for ObjectIdentifier {
    open spec fn is_prefix_secure() -> bool {
        true
    }
    
    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        let b = self.spec_serialize(v);
        if v.len() >= 2 && v.len() <= usize::MAX {
            if let Some(first_byte) = Self::serialize_first_two_arcs(v[0], v[1]) {
                let rest_arcs = v.skip(2);
                let buf = (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs));

                new_spec_object_identifier_inner().theorem_serialize_parse_roundtrip((buf.len() as LengthValue, (first_byte, rest_arcs)));
                Self::lemma_serialize_parse_first_two_arcs(v[0], v[1]);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Some((len, v)) = self.spec_parse(buf) {
            if let Some((_, (_, (first_byte, rest_arcs)))) = new_spec_object_identifier_inner().spec_parse(buf) {
                new_spec_object_identifier_inner().theorem_parse_serialize_roundtrip(buf);
                Self::lemma_parse_serialize_first_two_arcs(first_byte);

                assert(v.skip(2) =~= rest_arcs);

                let buf2 = self.spec_serialize(v);
                assert(buf2 =~= buf.subrange(0, len));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_object_identifier_inner().lemma_prefix_secure(s1, s2);
    }
    
    proof fn lemma_parse_length(&self, s: Seq<u8>) {}
    
    proof fn lemma_parse_productive(&self, s: Seq<u8>) {}
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for ObjectIdentifier {
    type Type = ObjectIdentifierValue;
    type SType = &'a Self::Type;

    fn length(&self, v: Self::SType) -> usize {
        let ghost v_spec = v@;

        let first = v.0 .0[0];
        let second = v.0 .0[1];

        let first_byte = (first as u8) * 40 + (second as u8);

        let mut rest_arcs_clone = Clone::clone(&v.0 .0);
        let rest_arcs = RepeatResult(rest_arcs_clone.split_off(2));
        let inner_args = (&first_byte, &rest_arcs);
        let ghost rest_spec = rest_arcs@;

        proof {
            assert(rest_spec == v_spec.skip(2));
            assert(Self::serialize_first_two_arcs(first, second) == Some(first_byte));
            let payload = (U8, Repeat(Base128UInt))@.spec_serialize((first_byte, rest_spec));
            assert(payload.len() <= usize::MAX);
            assert(new_spec_object_identifier_inner().wf((payload.len() as LengthValue, (first_byte, rest_spec))));
        }

        let len_inner = (U8, Repeat(Base128UInt)).length(inner_args);
        let length_value: LengthValue = len_inner;
        let inner = new_object_identifier_inner();
        let len_total = inner.length((length_value, inner_args));

        assert(len_total == self@.spec_serialize(v_spec).len());

        len_total
    }

    #[inline]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
    let (len, (_, (first, mut rest_arcs))) = new_object_identifier_inner().parse(s)?;

        let arc1 = first / 40;
        let arc2 = first % 40;

        if arc1 > 2 || arc2 > 39 {
            return Err(ParseError::Other("Invalid first two arcs".to_string()));
        }

        if rest_arcs.0.len() > usize::MAX - 2 {
            return Err(ParseError::Other("OID arcs exceed maximum length".to_string()));
        }

        let mut res = Vec::with_capacity(2 + rest_arcs.0.len());
        res.push(arc1 as UInt);
        res.push(arc2 as UInt);
        res.append(&mut rest_arcs.0);

        let res = Ok((len, ObjectIdentifierValue(RepeatResult(res))));

        assert(
            self@.spec_parse(s@) matches Some((n, v)) ==> res matches Ok((m, u)) && m == n && v
                == u@
        );
        res

    }

    #[inline]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let ghost old_v = v@;

        if v.0.0.len() < 2 {
            return Err(SerializeError::Other("OID should have at least two arcs".to_string()));
        }

        if v.0.0[0] > 2 || v.0.0[1] > 39 {
            return Err(SerializeError::Other("Invalid first two arcs".to_string()));
        }

        let first_byte = v.0.0[0] as u8 * 40 + v.0.0[1] as u8;
        let mut rest_arcs_clone = Clone::clone(&v.0.0);
        let rest_arcs = RepeatResult(rest_arcs_clone.split_off(2));

        let len = (U8, Repeat(Base128UInt)).serialize((&first_byte, &rest_arcs), data, pos)?;

        let ghost rest_arcs_spec = rest_arcs@;
        let length_value: LengthValue = len;
        let len2 = new_object_identifier_inner().serialize((length_value, (&first_byte, &rest_arcs)), data, pos)?;

        if pos.checked_add(len2).is_some() && pos + len2 <= data.len() {
            proof {
                assert(rest_arcs_spec == old_v.skip(2));
                assert(data@ =~= seq_splice(old(data)@, pos, self@.spec_serialize(old_v)));
            }

            return Ok(len2);
        }

        Err(SerializeError::InsufficientBuffer)
    }
}

/// The function |i| AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
struct OIDCont;

impl View for OIDCont {
    type V = spec_fn(LengthValue) -> AndThen<bytes::Variable, (U8, Repeat<Base128UInt>)>;

    open spec fn view(&self) -> Self::V {
        new_spec_object_identifier_inner().snd
    }
}

impl Continuation<POrSType<&LengthValue, LengthValue>> for OIDCont {
    type Output = AndThen<bytes::Variable, (U8, Repeat<Base128UInt>)>;

    open spec fn requires(&self, deps: POrSType<&LengthValue, LengthValue>) -> bool {
        true
    }

    open spec fn ensures(&self, deps: POrSType<&LengthValue, LengthValue>, o: Self::Output) -> bool {
        o@ == (self@)(deps@)
    }

    fn apply(&self, deps: POrSType<&LengthValue, LengthValue>) -> (o: Self::Output) {
        let i = match deps {
            POrSType::P(i) => *i,
            POrSType::S(i) => i,
        };
        AndThen(bytes::Variable(i as usize), (U8, Repeat(Base128UInt)))
    }
}

/// The inner version parses a length first
/// then read a single byte (for the first two arcs)
/// and then repeatedly read a sequence of Base128UInt's
#[allow(dead_code)]
type SpecObjectIdentifierInner = SpecDepend<Length, AndThen<bytes::Variable, (U8, Repeat<Base128UInt>)>>;
type ObjectIdentifierInner = Depend<Length, AndThen<bytes::Variable, (U8, Repeat<Base128UInt>)>, OIDCont>;

pub closed spec fn new_spec_object_identifier_inner() -> SpecObjectIdentifierInner {
    Pair::spec_new(Length, |l| AndThen(bytes::Variable(l as usize), (U8, Repeat(Base128UInt))))
}

#[inline(always)]
fn new_object_identifier_inner() -> (res: ObjectIdentifierInner)
    ensures res@ == new_spec_object_identifier_inner()
{
    Pair::new(Length, OIDCont)
}

}

impl Debug for ObjectIdentifierValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "OID(")?;

        for (i, arc) in self.0 .0.iter().enumerate() {
            if i != 0 {
                write!(f, ".")?;
            }

            write!(f, "{}", arc)?;
        }

        write!(f, ")")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use der::Encode;

    fn serialize_oid(v: Vec<UInt>) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; 1 + 4 + v.len() * 8];
        data[0] = 0x06;
        let len = ObjectIdentifier.serialize(
            &ObjectIdentifierValue(RepeatResult(v)),
            &mut data,
            1,
        )?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        let diff = |v: Vec<UInt>| {
            let res1 = serialize_oid(PolyfillClone::clone(&v)).map_err(|_| ());
            let res2 = der::asn1::ObjectIdentifier::new_unwrap(
                v.iter()
                    .map(|i| i.to_string())
                    .collect::<Vec<_>>()
                    .join(".")
                    .as_str(),
            )
            .to_der()
            .map_err(|_| ());

            assert_eq!(res1, res2);
        };

        diff(vec![1, 2, 3]);
        diff(vec![1, 2, 123214]);
        diff(vec![1, 2, 123214, 1231, 4534, 231]);
        diff(vec![2, 10, 123214, 1231, 4534, 231]);
        diff(vec![2, 39, 123214, 1231, 4534, 231]);
    }
}
