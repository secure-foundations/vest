#[test]
fn only_dependent_fields_request_value_soundness() {
    let generated = vest::compile(
        "dependencies.vest",
        "message = { @length: u8, data: [u8; @length], }".to_string(),
    )
    .expect("compile a dependent length");

    assert!(generated.contains("(U8).lemma_parse_sound_value(rest@);"));
    assert!(!generated.contains("broadcast use vest_lib::core::spec::SoundParser::"));
    assert!(!generated.contains("broadcast use vest_lib::core::spec::StrictParser::"));
}
