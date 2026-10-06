//! Rustls' owned-buffer entry point with caller-owned input lifetime.

use rustls::internal::msgs::base::Payload;
use rustls::internal::msgs::handshake::HandshakeMessagePayload;
use rustls::internal::msgs::message::MessagePayload;
use rustls::{ContentType, ProtocolVersion};

pub fn parse(payload: &mut Payload) -> HandshakeMessagePayload {
    // Restore the encoded buffer to its owner: parsing a borrowed Vest input
    // does not dispose of that input either. Parsed-value drops remain timed
    // on both sides; input creation and disposal are excluded on both sides.
    let owned = std::mem::replace(payload, Payload::new(Vec::new()));
    match MessagePayload::new(ContentType::Handshake, ProtocolVersion::TLSv1_3, owned).unwrap() {
        MessagePayload::Handshake { parsed, encoded } => {
            *payload = encoded;
            parsed
        }
        _ => unreachable!(),
    }
}
