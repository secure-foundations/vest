use super::*;
use vstd::prelude::*;
use vstd::vstd::slice::slice_subrange;

verus! {

/// Combainator for UTF8String in ASN.1
#[derive(Debug, View)]
pub struct UTF8String;

asn1_tagged!(UTF8String, tag_of!(UTF8_STRING));

pub type SpecUTF8StringValue = Seq<char>;
pub type UTF8StringValue<'a> = &'a str;
pub type UTF8StringValueOwned = String;

impl SpecCombinator for UTF8String {
    type SpecResult = SpecUTF8StringValue;

    closed spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::SpecResult), ()> {
        match Length.spec_parse(s) {
            Ok((n, l)) => {
                if n + l <= usize::MAX && n + l <= s.len() {
                    match spec_parse_utf8(s.skip(n as int).take(l as int)) {
                        Some(parsed) => Ok(((n + l) as usize, parsed)),
                        None => Err(()),
                    }
                } else {
                    Err(())
                }
            }
            Err(()) => Err(()),
        }
    }

    proof fn spec_parse_wf(&self, s: Seq<u8>) {}

    closed spec fn spec_serialize(&self, v: Self::SpecResult) -> Result<Seq<u8>, ()> {
        let s = spec_serialize_utf8(v);
        match Length.spec_serialize(s.len() as LengthValue) {
            Ok(buf) =>
                if buf.len() + s.len() <= usize::MAX {
                    Ok(buf + s)
                } else {
                    Err(())
                },
            Err(()) => Err(()),
        }
    }
}

impl SecureSpecCombinator for UTF8String {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::SpecResult) {
        let s = spec_serialize_utf8(v);

        Length.theorem_serialize_parse_roundtrip(s.len() as LengthValue);
        spec_utf8_serialize_parse_roundtrip(v);

        if let Ok(buf) = Length.spec_serialize(s.len() as LengthValue)  {
            if buf.len() + s.len() <= usize::MAX {
                Length.lemma_prefix_secure(buf, s);
                assert((buf + s).skip(buf.len() as int).take(s.len() as int) == s);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, buf: Seq<u8>) {
        if let Ok((n, l)) = Length.spec_parse(buf) {
            if n + l <= buf.len() {
                let s = buf.skip(n as int).take(l as int);

                Length.theorem_parse_serialize_roundtrip(buf);
                spec_utf8_parse_serialize_roundtrip(s);
                assert(buf.subrange(0, (n + l) as int) == buf.subrange(0, n as int) + buf.skip(n as int).take(l as int));
            }
        }
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) {
        Length.lemma_prefix_secure(s1, s2);

        if let Ok((n, l)) = Length.spec_parse(s1) {
            if n + l <= s1.len() {
                assert(s1.skip(n as int).take(l as int) =~= (s1 + s2).skip(n as int).take(l as int));
            }
        }
    }
}

impl Combinator for UTF8String {
    type Result<'a> = UTF8StringValue<'a>;
    type Owned = UTF8StringValueOwned;

    closed spec fn spec_length(&self) -> Option<usize> {
        None
    }

    fn length(&self) -> Option<usize> {
        None
    }

    #[inline(always)]
    fn parse<'a>(&self, s: &'a [u8]) -> (res: Result<(usize, Self::Result<'a>), ParseError>) {
        let (n, l) = Length.parse(s)?;

        if let Some(total_len) = n.checked_add(l as usize) {
            if total_len <= s.len() {
                match utf8_to_str(slice_take(slice_subrange(s, n, s.len()), l as usize)) {
                    Some(parsed) => Ok((total_len, parsed)),
                    _ => Err(ParseError::Other("Invalid UTF-8".to_string()))
                }
            } else {
                Err(ParseError::UnexpectedEndOfInput)
            }
        } else {
            Err(ParseError::SizeOverflow)
        }
    }

    #[inline(always)]
    fn serialize(&self, v: Self::Result<'_>, data: &mut Vec<u8>, pos: usize) -> (res: Result<usize, SerializeError>) {
        let s = str_to_utf8(v);
        let n = Length.serialize(s.len() as LengthValue, data, pos)?;

        if pos.checked_add(n).is_none() {
            return Err(SerializeError::SizeOverflow);
        }

        if (pos + n).checked_add(s.len()).is_none() {
            return Err(SerializeError::SizeOverflow);
        }

        if pos + n + s.len() >= data.len() {
            return Err(SerializeError::InsufficientBuffer);
        }

        let ghost data_after_len = data@;

        // No Vec::splice yet in Verus
        for i in 0..s.len()
            invariant
                pos + n + s.len() <= usize::MAX,
                pos + n + s.len() < data.len() == data_after_len.len(),

                data@ =~= seq_splice(data_after_len, (pos + n) as usize, s@.take(i as int)),
        {
            data.set(pos + n + i, s[i]);
        }

        assert(data@ =~= seq_splice(old(data)@, pos, Length.spec_serialize(s@.len() as LengthValue).unwrap() + s@));

        Ok(n + s.len())
    }
}

}

#[cfg(test)]
mod test {
    use super::*;
    use der::Encode;

    fn serialize_utf8_string(v: &str) -> Result<Vec<u8>, SerializeError> {
        let mut data = vec![0; v.len() + 10];
        data[0] = 0x0c; // Prepend the tag byte
        let len = UTF8String.serialize(v, &mut data, 1)?;
        data.truncate(len + 1);
        Ok(data)
    }

    #[test]
    fn diff_with_der() {
        let diff = |s: &str| {
            let res1 = serialize_utf8_string(s).map_err(|_| ());
            let res2 = s.to_string().to_der().map_err(|_| ());
            assert_eq!(res1, res2);
        };

        diff("");
        diff("asdsad");
        diff("黑风雷");
        diff("👨‍👩‍👧‍👦");
        diff("黑风雷".repeat(256).as_str());
    }
}
