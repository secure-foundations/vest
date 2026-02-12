use super::*;
use vstd::prelude::*;

verus! {

/// Combainator for OCTET STRING in ASN.1
#[derive(Debug, View)]
pub struct OctetString;

asn1_tagged!(OctetString, tag_of!(OCTET_STRING));

impl SpecCombinator for OctetString {
    type Type = Seq<u8>;

    open spec fn wf(&self, v: Self::Type) -> bool {
        new_spec_octet_string_inner().wf((v.len() as LengthValue, v))
    }

    open spec fn requires(&self) -> bool {
        new_spec_octet_string_inner().requires()
    }

    open spec fn spec_parse(&self, s: Seq<u8>) -> Option<(int, Self::Type)> {
        match new_spec_octet_string_inner().spec_parse(s) {
            Some((len, (_, v))) => Some((len, v)),
            None => None,
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Seq<u8> {
        new_spec_octet_string_inner().spec_serialize((v.len() as LengthValue, v))
    }
}

impl SecureSpecCombinator for OctetString {
    open spec fn is_prefix_secure() -> bool {
        SpecOctetStringInner::is_prefix_secure()
    }

    open spec fn is_productive(&self) -> bool {
        new_spec_octet_string_inner().is_productive()
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type) {
        new_spec_octet_string_inner().theorem_serialize_parse_roundtrip((v.len() as LengthValue, v));
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_octet_string_inner().theorem_parse_serialize_roundtrip(buf);
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_octet_string_inner().lemma_prefix_secure(s1, s2);
    }

    proof fn lemma_parse_length(&self, s: Seq<u8>) {
        new_spec_octet_string_inner().lemma_parse_length(s);
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) {
        new_spec_octet_string_inner().lemma_parse_productive(s);
    }
}

impl OctetString {
    pub proof fn lemma_wf_always(v: Seq<u8>)
        requires v.len() <= usize::MAX as int
        ensures OctetString.wf(v)
    {
        assert(v.len() as usize as int == v.len());
    }
}

impl<'a> Combinator<'a, &'a [u8], Vec<u8>> for OctetString {
    type Type = &'a [u8];
    type SType = &'a Self::Type;

    fn length(&self, v: Self::SType) -> usize {
        let bytes = *v;
        new_octet_string_inner().length((bytes.len() as LengthValue, &bytes))
    }

    #[inline(always)]
    fn parse(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Type), ParseError>) {
        let (len, (_, v)) = new_octet_string_inner().parse(s)?;
        Ok((len, v))
    }

    #[inline(always)]
    fn serialize(&self, v: Self::SType, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let bytes = *v;
        new_octet_string_inner().serialize((bytes.len() as LengthValue, &bytes), data, pos)
    }
}

/// The function |i| Variable(i)
struct BytesCont;

impl View for BytesCont {
    type V = spec_fn(LengthValue) -> bytes::Variable;

    open spec fn view(&self) -> Self::V {
        new_spec_octet_string_inner().snd
    }
}

impl Continuation<POrSType<&LengthValue, LengthValue>> for BytesCont {
    type Output = bytes::Variable;

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
        bytes::Variable(i as usize)
    }
}

#[allow(dead_code)]
type SpecOctetStringInner = SpecDepend<Length, bytes::Variable>;
type OctetStringInner = Depend<Length, bytes::Variable, BytesCont>;

pub closed spec fn new_spec_octet_string_inner() -> SpecOctetStringInner {
    Pair::spec_new(Length, |l| bytes::Variable(l as usize))
}

#[inline(always)]
fn new_octet_string_inner() -> (res: OctetStringInner)
    ensures
        res@ == new_spec_octet_string_inner(),
{
    Pair::new(Length, BytesCont)
}

}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    fn serialize_octet_string(v: &[u8]) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.len() + 10];
        data[0] = 0x04; // Prepend the tag byte
        let len = OctetString.serialize(&v, &mut data, 1)?;
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
