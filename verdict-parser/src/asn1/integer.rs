use super::*;
use vstd::prelude::*;

verus! {

/// Combinator for ASN.1 integers (without the preceding tag)
/// This combinator uses IntegerInner with the additional constraint
/// of is_min_num_bytes_signed
#[derive(Debug, View)]
pub struct Integer;

asn1_tagged!(Integer, tag_of!(INTEGER));

pub type IntegerValue = VarIntResult;

impl SpecCombinator for Integer {
    type SpecResult = IntegerValue;

    /// Same as new_spec_integer_inner(), but filters out tuples (n, v)
    /// where v is *not* the minimum number of bytes required to represent v
    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match new_spec_integer_inner().spec_parse(s) {
            Ok((len, (n, v))) => {
                if is_min_num_bytes_signed(v, n as VarUIntResult) {
                    Ok((len, v))
                } else {
                    Err(())
                }
            }
            Err(..) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {
        new_spec_integer_inner().spec_parse_wf(s);
    }

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        new_spec_integer_inner().spec_serialize((min_num_bytes_signed(v) as LengthValue, v))
    }
}

impl SecureSpecCombinator for Integer {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        new_spec_integer_inner().theorem_serialize_parse_roundtrip((min_num_bytes_signed(v) as LengthValue, v));
        lemma_min_num_bytes_signed(v);
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        new_spec_integer_inner().theorem_parse_serialize_roundtrip(buf);

        if let Ok((_, (n, v))) = new_spec_integer_inner().spec_parse(buf) {
            lemma_min_num_bytes_signed(v);
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        new_spec_integer_inner().lemma_prefix_secure(s1, s2);
    }
}

impl Combinator for Integer {
    type Result<'a> = IntegerValue;
    type Owned = IntegerValue;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (len, (n, v)) = new_integer_inner().parse(s)?;

        if is_min_num_bytes_signed_exec(v, n as VarUIntResult) {
            Ok((len, v))
        } else {
            Err(ParseError::Other("Non-minimal integer encoding".to_string()))
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        proof {
            lemma_min_num_bytes_signed(v);
        }
        new_integer_inner().serialize((min_num_bytes_signed_exec(v) as LengthValue, v), data, pos)
    }
}

/// This is a function that takes in a VarUIntResult (`l`)
/// and returns a VarInt combinator that reads `l` bytes
struct IntegerCont;

impl Continuation for IntegerCont {
    type Input<'a> = LengthValue;
    type Output = VarInt;

    #[inline(always)]
    fn apply<'a>(&self, i: Self::Input<'a>) -> (o: Self::Output) {
        VarInt(i as usize)
    }

    closed spec fn requires<'a>(&self, i: Self::Input<'a>) -> bool {
        true
    }

    closed spec fn ensures<'a>(&self, i: Self::Input<'a>, o: Self::Output) -> bool {
        o == VarInt(i as usize)
    }
}

/// A combinator that parses (n, v) where v is a VarInt parsed from n bytes
/// This does not check if n is the minimum number of bytes required to represent v
#[allow(dead_code)]
type SpecIntegerInner = SpecDepend<Length, VarInt>;
type IntegerInner = Depend<Length, VarInt, IntegerCont>;

closed spec fn new_spec_integer_inner() -> SpecIntegerInner {
    let ghost spec_snd = |l| {
        VarInt(l as usize)
    };

    SpecDepend {
        fst: Length,
        snd: spec_snd,
    }
}

#[inline(always)]
fn new_integer_inner() -> (res: IntegerInner)
    ensures res.view() == new_spec_integer_inner()
{
    let ghost spec_snd = |l| {
        VarInt(l as usize)
    };

    Depend {
        fst: Length,
        snd: IntegerCont,
        spec_snd: Ghost(spec_snd),
    }
}

}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    #[test]
    fn parse() {
        assert_eq!(Integer.parse(&[0x01, 0x00]).unwrap(), (2, 0));
        assert_eq!(Integer.parse(&[0x01, 0xff]).unwrap(), (2, -1));
        assert_eq!(Integer.parse(&[0x02, 0x00, 0xff]).unwrap(), (3, 0xff));

        assert!(Integer.parse(&[0x00]).is_err());
        assert!(Integer.parse(&[0x81, 0x01, 0xff]).is_err());
        assert!(Integer.parse(&[0x02, 0x00, 0x7f]).is_err()); // violation of minimal encoding
    }

    fn serialize_int(v: IntegerValue) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; 16];
        let len = ASN1(Integer).serialize(v, &mut data, 0)?;
        data.truncate(len);
        Ok(data)
    }

    /// Compare results of serialize to a common ASN.1 DER library
    #[test]
    fn diff_with_der() {
        let diff = |i| {
            let res1 = serialize_int(i).map_err(|_| ());
            let res2 = i.to_der().map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff(0);
        diff(i64::MAX);
        diff(i64::MIN);

        for i in 0..65535i64 {
            diff(i);
        }

        for i in -65535i64..0 {
            diff(i);
        }
    }
}
