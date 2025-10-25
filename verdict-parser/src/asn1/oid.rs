use super::*;
use std::fmt::{self, Debug, Formatter};
use vstd::prelude::*;

verus! {

/// Combinator for ASN.1 Object Identifier
#[derive(Debug, View)]
pub struct ObjectIdentifier;

asn1_tagged!(ObjectIdentifier, tag_of!(OBJECT_IDENTIFIER));

pub type SpecObjectIdentifierValue = Seq<UInt>;
#[derive(PolyfillClone, Eq, PartialEq)]
pub struct ObjectIdentifierValue(pub VecDeep<UInt>);
pub type ObjectIdentifierValueOwned = ObjectIdentifierValue;

impl View for ObjectIdentifierValue {
    type V = Seq<UInt>;

    open spec fn view(&self) -> Self::V {
        self.0@
    }
}

impl PolyfillEq for ObjectIdentifierValue {
    #[inline(always)]
    fn polyfill_eq(&self, other: &ObjectIdentifierValue) -> bool
    {
        self.0.polyfill_eq(&other.0)
    }
}

impl ObjectIdentifier {
    /// First byte of an OID is 40 * arc1 + arc2
    closed spec fn parse_first_two_arcs(byte: u8) -> Option<(UInt, UInt)> {
        let arc1 = byte / 40;
        let arc2 = byte % 40;

        if arc1 <= 2 && arc2 <= 39 {
            Some((arc1 as UInt, arc2 as UInt))
        } else {
            None
        }
    }

    closed spec fn serialize_first_two_arcs(arc1: UInt, arc2: UInt) -> Option<u8> {
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
    type SpecResult = SpecObjectIdentifierValue;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_object_identifier_inner().spec_parse(s) {
            Ok((len, (_, (first, rest_arcs)))) =>
                match Self::parse_first_two_arcs(first) {
                    Some((arc1, arc2)) =>
                        if rest_arcs.len() + 2 <= usize::MAX {
                            Ok((len, seq![ arc1, arc2 ] + rest_arcs))
                        } else {
                            Err(())
                        }
                    None => Err(()),
                }

            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_object_identifier_inner().spec_parse_wf(s);
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        if v.len() < 2 || v.len() > usize::MAX {
            Err(())
        } else {
            match Self::serialize_first_two_arcs(v[0], v[1]) {
                Some(first_byte) => {
                    let rest_arcs = v.skip(2);

                    // Compute the inner length first
                    // TODO: how to avoid this?
                    match (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs)) {
                        Ok(buf) =>
                            new_spec_object_identifier_inner().spec_serialize((buf.len() as LengthValue, (first_byte, rest_arcs))),
                        Err(..) => Err(())
                    }
                },
                None => Err(()),
            }
        }
    }
}

impl SecureSpecCombinator for ObjectIdentifier {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        if let Ok(b) = self.spec_serialize(v) {
            let first_byte = Self::serialize_first_two_arcs(v[0], v[1]).unwrap();
            let rest_arcs = v.skip(2);
            let buf = (U8, Repeat(Base128UInt)).spec_serialize((first_byte, rest_arcs)).unwrap();

            new_spec_object_identifier_inner().theorem_serialize_parse_roundtrip((buf.len() as LengthValue, (first_byte, rest_arcs)));
            Self::lemma_serialize_parse_first_two_arcs(v[0], v[1]);

            let (len, v2) = self.spec_parse(b).unwrap();
            assert(len == b.len() as usize);
            assert(v2 =~= v);
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((len, v)) = self.spec_parse(buf) {
            let (_, (_, (first_byte, rest_arcs))) = new_spec_object_identifier_inner().spec_parse(buf).unwrap();

            new_spec_object_identifier_inner().theorem_parse_serialize_roundtrip(buf);
            Self::lemma_parse_serialize_first_two_arcs(first_byte);

            assert(v.skip(2) =~= rest_arcs);

            let buf2 = self.spec_serialize(v).unwrap();
            assert(buf2 =~= buf.subrange(0, len as int));
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_object_identifier_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for ObjectIdentifier {
    type Result<'a> = ObjectIdentifierValue;
    type Owned = ObjectIdentifierValueOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, (_, (first, mut rest_arcs))) = new_object_identifier_inner().parse(s)?;

        let arc1 = first / 40;
        let arc2 = first % 40;

        if arc1 > 2 || arc2 > 39 {
            return Err(ParseError::Other("Invalid first two arcs".to_string()));
        }

        if rest_arcs.len() > usize::MAX - 2 {
            return Err(ParseError::SizeOverflow);
        }

        let mut res = VecDeep::with_capacity(2 + rest_arcs.len());
        res.push(arc1 as UInt);
        res.push(arc2 as UInt);
        res.append(&mut rest_arcs);

        assert(res@ == self.spec_parse(s@).unwrap().1);

        Ok((len, ObjectIdentifierValue(res)))
    }

    #[inline]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let mut v = v.0;
        let ghost old_v = v@;

        if v.len() < 2 {
            return Err(SerializeError::Other("OID should have at least two arcs".to_string()));
        }

        if *v.get(0) > 2 || *v.get(1) > 39 {
            return Err(SerializeError::Other("Invalid first two arcs".to_string()));
        }

        let first_byte = *v.get(0) as u8 * 40 + *v.get(1) as u8;

        let rest_arcs_inner = v.split_off(2);

        // Need to figure out the content length first
        // TODO: this seems inefficient
        let rest_arcs_cloned = PolyfillClone::clone(&rest_arcs_inner);
        let rest_arcs = rest_arcs_inner;

        let len = (U8, Repeat(Base128UInt)).serialize((first_byte, rest_arcs_cloned), data, pos)?;
        let len2 = new_object_identifier_inner().serialize((len as LengthValue, (first_byte, rest_arcs)), data, pos)?;

        if pos.checked_add(len2).is_some() && pos + len2 <= data.len() {
            assert(rest_arcs_cloned@ == old_v.skip(2));
            assert(data@ =~= seq_splice(old(data)@, pos, self.spec_serialize(old_v).unwrap()));

            return Ok(len2);
        }

        Err(SerializeError::InsufficientBuffer)
    }
}

/// The function |i| AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
struct OIDCont;

impl Continuation for OIDCont {
    type Input<'a> = LengthValue;
    type Output = AndThen<Bytes, (U8, Repeat<Base128UInt>)>;

    #[inline(always)]
    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
    }

    closed spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    closed spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == AndThen(Bytes(i as usize), (U8, Repeat(Base128UInt)))
    }
}

/// The inner version parses a length first
/// then read a single byte (for the first two arcs)
/// and then repeatedly read a sequence of Base128UInt's
#[allow(dead_code)]
type SpecObjectIdentifierInner = SpecDepend<Length, AndThen<Bytes, (U8, Repeat<Base128UInt>)>>;
type ObjectIdentifierInner = Depend<Length, AndThen<Bytes, (U8, Repeat<Base128UInt>)>, OIDCont>;

closed spec fn new_spec_object_identifier_inner() -> SpecObjectIdentifierInner {
    SpecDepend {
        fst: Length,
        snd: |l| {
            AndThen(Bytes(l as usize), (U8, Repeat(Base128UInt)))
        },
    }
}

#[inline(always)]
fn new_object_identifier_inner() -> (res: ObjectIdentifierInner)
    ensures res@ == new_spec_object_identifier_inner()
{
    Depend {
        fst: Length,
        snd: OIDCont,
        spec_snd: Ghost(|l| {
            AndThen(Bytes(l as usize), (U8, Repeat(Base128UInt)))
        }),
    }
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
            ObjectIdentifierValue(VecDeep::from_vec(v)),
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
