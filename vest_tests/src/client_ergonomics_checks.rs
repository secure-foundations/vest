#![allow(dead_code, unused_variables)]
use super::client_ergonomics::*;
use vest_lib::prelude::*;

verus! {

broadcast use parser_lemmas;
// Parsed values can be serialized directly, without preparation or revealing views.

fn message_parse_serialize(input: &[u8]) -> Result<Vec<u8>, ParseError> {
    let (consumed, value) = MessageFmt.parse(&input)?;
    let mut bytes = vec![0; consumed];
    MessageFmt.serialize(&value, &mut bytes);
    proof {
        MessageFmt.theorem_parse_serialize_roundtrip(input@);
    }
    assert(bytes@ == input@[0..consumed]);
    assert!(bytes.as_slice() == &input[..consumed]);
    Ok(bytes)
}

fn samples_parse_serialize(input: &[u8]) -> Result<Vec<u8>, ParseError> {
    let (consumed, value) = SamplesFmt.parse(&input)?;
    let mut bytes = vec![0; consumed];
    SamplesFmt.serialize(&value, &mut bytes);
    proof {
        SamplesFmt.theorem_parse_serialize_roundtrip(input@);
    }
    assert(bytes@ == input@[0..consumed]);
    assert!(bytes.as_slice() == &input[..consumed]);
    Ok(bytes)
}

fn choice_parse_serialize(input: &[u8]) -> Result<Vec<u8>, ParseError> {
    let (consumed, value) = VariableChoiceFmt.parse(&input)?;
    let mut bytes = vec![0; consumed];
    VariableChoiceFmt.serialize(&value, &mut bytes);
    proof {
        VariableChoiceFmt.theorem_parse_serialize_roundtrip(input@);
    }
    assert(bytes@ == input@[0..consumed]);
    assert!(bytes.as_slice() == &input[..consumed]);
    Ok(bytes)
}

// Only the public view is revealed to compare fields; the parser stays opaque.
fn message_non_malleability(first: &[u8], second: &[u8]) -> Result<bool, ParseError> {
    proof {
        reveal(<Message as DeepView>::deep_view);
    }
    let (n1, left) = MessageFmt.parse(&first)?;
    let (n2, right) = MessageFmt.parse(&second)?;
    if left.length == right.length && left.payload == right.payload {
        proof {
            // Establish extensional equality before using the theorem's implication.
            assert(left.deep_view() == right.deep_view());
            MessageFmt.lemma_parse_non_malleable(first@, second@);
        }
        assert(first@[0..n1] == second@[0..n2]);
        assert!(first[..n1] == second[..n2]);
        Ok(true)
    } else {
        Ok(false)
    }
}

proof fn same_model_has_unique_encoding(
    first: Seq<u8>,
    second: Seq<u8>,
    n1: int,
    n2: int,
    value: MessageSpec,
)
    requires
        MessageFmt.spec_parse(first) == Some((n1, value)),
        MessageFmt.spec_parse(second) == Some((n2, value)),
    ensures
        first[0..n1] == second[0..n2],
{
    MessageFmt.corollary_parse_non_malleable(first, second);
}

proof fn distinct_messages_have_distinct_encodings(left: MessageSpec, right: MessageSpec)
    requires
        MessageFmt.consistent(left),
        MessageFmt.consistent(right),
        left != right,
    ensures
        MessageFmt.spec_serialize(left) != MessageFmt.spec_serialize(right),
{
    MessageFmt.corollary_serialize_injective_contrapositive(left, right);
}

fn triple_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<Triple as DeepView>::deep_view);
    }
    let value = Triple { a: 0x42, b: [0x55, 0x77], c: u64::MAX };
    let len = TripleFmt.prepare(&value)?;
    assert(len == 11);
    assert!(len == 11);
    let mut bytes = vec![0; len];
    TripleFmt.serialize(&value, &mut bytes);
    proof {
        TripleFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = TripleFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == 11);
    assert(parsed.a == 0x42);
    assert(parsed.b@ == value.b@);
    assert(parsed.c == u64::MAX);
    assert!(consumed == 11);
    assert!(parsed.a == 0x42);
    assert!(parsed.b.as_slice() == value.b.as_slice());
    assert!(parsed.c == u64::MAX);
    Ok(())
}

fn alias_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<TripleAlias as DeepView>::deep_view);
    }
    let value = TripleAlias { a: 1, b: [0x55, 0x77], c: 2 };
    let len = TripleAliasFmt.prepare(&value)?;
    assert(len == 11);
    assert!(len == 11);
    let mut bytes = vec![0; len];
    TripleAliasFmt.serialize(&value, &mut bytes);
    proof {
        TripleAliasFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = TripleAliasFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.a == 1);
    assert!(consumed == len);
    assert!(parsed.a == 1);
    Ok(())
}

fn message_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<Message as DeepView>::deep_view);
        reveal(<MessageFmt as SpecByteLen>::byte_len);
    }
    let payload = [b'a', b'b', b'c'];
    let value = Message { length: 3, payload: payload.as_slice() };
    let len = MessageFmt.prepare(&value)?;
    assert(len == 5);
    assert!(len == 5);
    let mut bytes = vec![0; len];
    MessageFmt.serialize(&value, &mut bytes);
    proof {
        MessageFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = MessageFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.length == 3);
    assert(parsed.payload@ == payload@);
    assert(parsed.payload[0] == b'a');
    assert!(consumed == len);
    assert!(parsed.length == 3);
    assert!(parsed.payload == payload.as_slice());
    assert!(parsed.payload[0] == b'a');
    Ok(())
}

fn samples_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<Samples as DeepView>::deep_view);
        reveal(<SamplesFmt as SpecByteLen>::byte_len);
    }
    let value = Samples { count: 2, values: vec![100u16, 200u16] };
    let len = SamplesFmt.prepare(&value)?;
    assert(len == 6);
    assert!(len == 6);
    let mut bytes = vec![0; len];
    SamplesFmt.serialize(&value, &mut bytes);
    proof {
        SamplesFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = SamplesFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.count == 2);
    assert(parsed.values@ == value.values@);
    assert!(consumed == len);
    assert!(parsed.count == 2);
    assert!(parsed.values == value.values);
    Ok(())
}

fn samples_length(value: Samples) -> Result<(), PreSerializeError> {
    proof {
        reveal(<Samples as DeepView>::deep_view);
        reveal(<SamplesFmt as SpecByteLen>::byte_len);
    }
    let len = SamplesFmt.prepare(&value)?;
    assert(len == 2 + 2 * value.values@.len());
    assert!(len == 2 + 2 * value.values.len());
    Ok(())
}

fn fixed_window_roundtrip() -> Result<(), PreSerializeError> {
    let payload = [1u8, 2, 3];
    let value = payload.as_slice();
    let len = FixedWindowFmt.prepare(&value)?;
    assert(len == 3);
    assert!(len == 3);
    let mut bytes = vec![0; len];
    FixedWindowFmt.serialize(&value, &mut bytes);
    proof {
        FixedWindowFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = FixedWindowFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed@ == payload@);
    assert!(consumed == len);
    assert!(parsed == payload.as_slice());
    Ok(())
}

fn fixed_choice_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<FixedChoice as DeepView>::deep_view);
    }
    let value = FixedChoice::High(200);
    let len = FixedChoiceFmt.prepare(&value)?;
    assert(len == 1);
    assert!(len == 1);
    let mut bytes = vec![0; len];
    FixedChoiceFmt.serialize(&value, &mut bytes);
    proof {
        FixedChoiceFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = FixedChoiceFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed matches FixedChoice::High(x) && x == 200);
    assert!(consumed == len);
    assert!(matches!(parsed, FixedChoice::High(200)));
    Ok(())
}

fn variable_choice_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<VariableChoice as DeepView>::deep_view);
        reveal(<VariableChoiceFmt as SpecByteLen>::byte_len);
    }
    let value = VariableChoice::Long(2);
    let len = VariableChoiceFmt.prepare(&value)?;
    assert(len == 3);
    assert!(len == 3);
    let mut bytes = vec![0; len];
    VariableChoiceFmt.serialize(&value, &mut bytes);
    proof {
        VariableChoiceFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = VariableChoiceFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed matches VariableChoice::Long(x) && x == 2);
    assert!(consumed == len);
    assert!(matches!(parsed, VariableChoice::Long(2)));
    Ok(())
}

fn nested_roundtrip() -> Result<(), PreSerializeError> {
    proof {
        reveal(<Envelope as DeepView>::deep_view);
        reveal(<Message as DeepView>::deep_view);
        reveal(<EnvelopeFmt as SpecByteLen>::byte_len);
    }
    let payload = [10u8, 20, 30];
    let message = Message { length: 3, payload: payload.as_slice() };
    let child_len = MessageFmt.prepare(&message)?;
    let value = Envelope { kind: 7, message };
    let len = EnvelopeFmt.prepare(&value)?;
    assert(len == 1 + child_len);
    assert!(len == 1 + child_len);
    let mut bytes = vec![0; len];
    EnvelopeFmt.serialize(&value, &mut bytes);
    proof {
        EnvelopeFmt.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = EnvelopeFmt.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.kind == 7);
    assert(parsed.message.deep_view() == message.deep_view());
    assert(parsed.message.length == message.length);
    assert(parsed.message.payload@ == message.payload@);
    assert!(consumed == len);
    assert!(parsed.kind == 7);
    assert!(parsed.message.length == message.length);
    assert!(parsed.message.payload == message.payload);
    Ok(())
}

fn parameterized_roundtrip(format: BoundedFmt) -> Result<(), PreSerializeError>
    requires
        format.length_spec() == 3,
{
    proof {
        reveal(<Bounded as DeepView>::deep_view);
        reveal(<BoundedFmt as SpecByteLen>::byte_len);
    }
    let payload = [1u8, 2, 3];
    let value = Bounded { payload: payload.as_slice() };
    let len = format.prepare(&value)?;
    assert(len == 3);
    assert!(len == 3);
    let mut bytes = vec![0; len];
    format.serialize(&value, &mut bytes);
    proof {
        format.theorem_serialize_parse_roundtrip(value.deep_view());
    }
    let (consumed, parsed) = format.parse(&bytes.as_slice()).unwrap();
    assert(consumed == len);
    assert(parsed.payload@ == payload@);
    assert!(consumed == len);
    assert!(parsed.payload == payload.as_slice());
    Ok(())
}

proof fn invalid_fixed_bytes_do_not_have_a_static_length() {
    let value = seq![1u8];
    assert(!Fixed::<2>.consistent(value));
    assert(Fixed::<2>.byte_len(value) == 1);
    assert(<Fixed<2> as StaticByteLen>::static_byte_len() == 2);
}

struct NonIdentity {
    byte: u8,
}

impl DeepView for NonIdentity {
    type V = Self;

    closed spec fn deep_view(&self) -> Self {
        Self { byte: (255 - self.byte) as u8 }
    }
}

// V = Self alone does not imply identity. The default vector lemma must not
// erase a custom transformation merely because its output type is unchanged.
fn nonidentity_vector_views_remain_distinct() {
    let values = vec![NonIdentity { byte: 0 }];
    assert(values@[0].byte == 0);
    assert(values.deep_view()[0].byte == 255);
}

} // verus!
#[test]
fn parsed_values_reserialize_to_consumed_prefixes() {
    let message = [3, 0, b'a', b'b', b'c', 0xee];
    assert_eq!(message_parse_serialize(&message).unwrap(), message[..5]);
    let empty_message = [0, 0, 0xee];
    assert_eq!(
        message_parse_serialize(&empty_message).unwrap(),
        empty_message[..2]
    );
    let samples = [2, 0, 100, 0, 200, 0, 0xee];
    assert_eq!(samples_parse_serialize(&samples).unwrap(), samples[..6]);
    let empty_samples = [0, 0, 0xee];
    assert_eq!(
        samples_parse_serialize(&empty_samples).unwrap(),
        empty_samples[..2]
    );
    let choice = [2, 100, 0, 0xee];
    assert_eq!(choice_parse_serialize(&choice).unwrap(), choice[..3]);
    let short_choice = [1, 100, 0xee];
    assert_eq!(
        choice_parse_serialize(&short_choice).unwrap(),
        short_choice[..2]
    );
    assert!(message_parse_serialize(&[1, 0]).is_err());
    assert!(samples_parse_serialize(&[1, 0, 100]).is_err());
    assert!(choice_parse_serialize(&[3, 100]).is_err());
}

#[test]
fn equal_parsed_values_have_equal_consumed_prefixes() {
    let first = [3, 0, b'a', b'b', b'c', 0x11];
    let second = [3, 0, b'a', b'b', b'c', 0x22, 0x33];
    assert!(message_non_malleability(&first, &second).unwrap());
    assert_ne!(first.as_slice(), second.as_slice());
    assert!(!message_non_malleability(&first, &[3, 0, b'x', b'b', b'c']).unwrap());
    assert!(message_non_malleability(&first, &[3, 0]).is_err());
}

#[test]
fn executable_clients_roundtrip() {
    triple_roundtrip().unwrap();
    alias_roundtrip().unwrap();
    message_roundtrip().unwrap();
    samples_roundtrip().unwrap();
    fixed_window_roundtrip().unwrap();
    fixed_choice_roundtrip().unwrap();
    variable_choice_roundtrip().unwrap();
    nested_roundtrip().unwrap();
    samples_length(Samples {
        count: 0,
        values: vec![],
    })
    .unwrap();
    samples_length(Samples {
        count: 3,
        values: vec![1, 2, 3],
    })
    .unwrap();
}

#[test]
fn prepare_rejects_invalid_values() {
    let invalid = Triple {
        a: 1,
        b: [0, 0],
        c: 2,
    };
    assert!(TripleFmt.prepare(&invalid).is_err());
    let invalid = Message {
        length: 4,
        payload: &[1, 2, 3],
    };
    assert!(MessageFmt.prepare(&invalid).is_err());
    let invalid = Samples {
        count: 1,
        values: vec![1, 2],
    };
    assert!(SamplesFmt.prepare(&invalid).is_err());
}

#[test]
fn successful_preparation_and_bytes_are_checked_at_runtime() {
    let value = Triple {
        a: 0x42,
        b: [0x55, 0x77],
        c: u64::MAX,
    };
    let len = TripleFmt.prepare(&value).unwrap();
    assert_eq!(len, 11);
    let mut bytes = vec![0; len];
    TripleFmt.serialize(&value, &mut bytes);
    let (consumed, parsed) = TripleFmt.parse(&bytes.as_slice()).unwrap();
    assert_eq!(consumed, 11);
    assert_eq!(parsed, value);

    let value = Samples {
        count: 2,
        values: vec![100, 200],
    };
    let len = SamplesFmt.prepare(&value).unwrap();
    assert_eq!(len, 6);
    let mut bytes = vec![0; len];
    SamplesFmt.serialize(&value, &mut bytes);
    assert_eq!(bytes, [2, 0, 100, 0, 200, 0]);
    assert_eq!(SamplesFmt.parse(&bytes.as_slice()).unwrap(), (len, value));
}
