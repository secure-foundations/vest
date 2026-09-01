use vest_lib::combinators::U16Be;
use vest_lib::core::exec::{Parser, Prepare, SerializerExt};

#[test]
fn documented_runtime_lifecycle_works() {
    let input: &[u8] = &[0x12, 0x34];
    let (consumed, value) = U16Be.parse(&input).unwrap();
    assert_eq!((consumed, value), (2, 0x1234));

    let len = U16Be.prepare(&value).unwrap();
    let mut output = vec![0; len];
    U16Be.serialize(&value, output.as_mut_slice());
    assert_eq!(output, input);
}
