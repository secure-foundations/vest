use rustls::internal::msgs::{base::Payload, codec::Codec};
use vest_bench::real::tls::{parse, tls_handshakes};
#[test]
fn tls_parse_retains_the_original_input_allocation() {
    for input in tls_handshakes() {
        let mut payload = Payload::new(input.bytes.clone());
        let pointer = payload.0.as_ptr();
        for _ in 0..2 {
            let parsed = parse(&mut payload);
            assert_eq!(payload.0.as_ptr(), pointer);
            assert_eq!(payload.0, input.bytes);
            let mut encoded = Vec::new();
            parsed.encode(&mut encoded);
            assert_eq!(encoded, input.bytes);
        }
    }
}
