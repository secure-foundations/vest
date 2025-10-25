use super::*;
use vstd::prelude::*;

verus! {

/// Combainator for OCTET STRING in ASN.1
#[derive(Debug, View)]
pub struct OctetString;

asn1_tagged!(OctetString, tag_of!(OCTET_STRING));

impl SpecCombinator for OctetString {
    type SpecResult = Seq<u8>;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_octet_string_inner().spec_parse(s) {
            Ok((len, (_, v))) => Ok((len, v)),
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_octet_string_inner().spec_parse_wf(s)
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_octet_string_inner().spec_serialize((v.len() as LengthValue, v))
    }
}

impl SecureSpecCombinator for OctetString {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_octet_string_inner().theorem_serialize_parse_roundtrip((v.len() as LengthValue, v));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_octet_string_inner().theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_octet_string_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for OctetString {
    type Result<'a> = &'a [u8];
    type Owned = Vec<u8>;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, (_, v)) = new_octet_string_inner().parse(s)?;
        Ok((len, v))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        new_octet_string_inner().serialize((v.len() as LengthValue, v), data, pos)
    }
}

/// The function |i| Bytes(i)
struct BytesCont;

impl Continuation for BytesCont {
    type Input<'a> = LengthValue;
    type Output = Bytes;

    #[inline(always)]
    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        Bytes(i as usize)
    }

    closed spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    closed spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        &&& o == Bytes(i as usize)
        &&& o.parse_requires()
        &&& o.serialize_requires()
    }
}

#[allow(dead_code)]
type SpecOctetStringInner = SpecDepend<Length, Bytes>;
type OctetStringInner = Depend<Length, Bytes, BytesCont>;

closed spec fn new_spec_octet_string_inner() -> SpecOctetStringInner {
    SpecDepend {
        fst: Length,
        snd: |l| {
            Bytes(l as usize)
        },
    }
}

closed spec fn spec_new_octet_string_inner() -> OctetStringInner
{
    Depend {
        fst: Length,
        snd: BytesCont,
        spec_snd: Ghost(|l| {
            Bytes(l as usize)
        }),
    }
}

#[inline(always)]
fn new_octet_string_inner() -> (res: OctetStringInner)
    ensures
        res@ == new_spec_octet_string_inner(),
        res == spec_new_octet_string_inner(),
{
    Depend {
        fst: Length,
        snd: BytesCont,
        spec_snd: Ghost(|l| {
            Bytes(l as usize)
        }),
    }
}

}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    fn serialize_octet_string(v: &[u8]) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.len() + 10];
        data[0] = 0x04; // Prepend the tag byte
        let len = OctetString.serialize(v, &mut data, 1)?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        let diff = |bytes: &[u8]| {
            let res1 = serialize_octet_string(bytes).map_err(|_| ());
            let res2 = der::asn1::OctetString::new(bytes)
                .unwrap()
                .to_der()
                .map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff(&[]);
        diff(&[0]);
        diff(&[0; 256]);
        diff(&[0; 257]);
        diff(&[0; 65536]);
    }
}
