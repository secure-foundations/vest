//! Complete-corpus agreement covers normalization and the bcder EXPLICIT wrapper.
use vest_bench::real::cms;
use vest_lib::core::exec::Parser;

#[test]
fn cms_codecs_agree_on_all_inputs() {
    cms::content_info_values(&cms::synthetic_content_info());
    let inputs = cms::real_signed_data();
    let common = cms::validated_signed_data(&inputs);
    cms::signed_data_values(&common);
}

#[test]
fn cms_repetitions_do_not_reserve_one_large_value_per_input_byte() {
    assert!(<_ as Parser<&[u8]>>::min_byte_len(&cms::SIGNED_DATA) > 0);
    for name in ["pkits/86e59bbb660905d7.cms", "dss/91b3289e675755c4.cms"] {
        let file = std::fs::read(vest_bench::real::corpora_dir().join("cms").join(name)).unwrap();
        let input = cms::signed_data(&file).unwrap();
        let (n, value) = cms::SIGNED_DATA.parse(&input).unwrap();
        assert_eq!(n, input.len());
        let certificates = value.certificates.as_ref().unwrap();
        assert!(
            certificates.capacity() <= 32,
            "{name}: capacity {}",
            certificates.capacity()
        );
        assert!(value.signer_infos.capacity() <= 64);
    }
}
