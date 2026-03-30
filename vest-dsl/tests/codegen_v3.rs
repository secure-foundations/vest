use std::path::PathBuf;

use vest::compile_v3;

fn manifest_path(parts: &[&str]) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for part in parts {
        path.push(part);
    }
    path
}

fn emitted_path(name: &str) -> PathBuf {
    manifest_path(&["tests", "emitted", &format!("{name}.rs")])
}

fn assert_v3_matches_checked_in_output(name: &str) {
    let vest_path = manifest_path(&["tests", "vest_files", &format!("{name}.vest")]);

    let input = std::fs::read_to_string(&vest_path).expect("read vest input");
    let v3 = compile_v3(vest_path.to_str().expect("utf-8 path"), input).expect("generate v3");
    let expected = std::fs::read_to_string(emitted_path(name)).expect("read emitted output");

    assert_eq!(
        v3, expected,
        "v3 output drifted from checked-in emitted output for {}",
        name
    );
}

fn compile_v3_from_rel(parts: &[&str]) -> String {
    let vest_path = manifest_path(parts);
    let input = std::fs::read_to_string(&vest_path).expect("read vest input");
    compile_v3(vest_path.to_str().expect("utf-8 path"), input).expect("generate v3")
}

#[test]
fn combined_output_matches_checked_in_output() {
    assert_v3_matches_checked_in_output("combined");
}

#[test]
fn tlv_output_matches_checked_in_output() {
    assert_v3_matches_checked_in_output("tlv");
}

#[test]
fn single_field_struct_stays_nominal_in_v3() {
    let v3 = compile_v3_from_rel(&["tests", "vest_files", "single_field.vest"]);

    assert!(
        v3.contains("pub struct Single"),
        "expected v3 to emit a nominal struct for single-field definitions"
    );
    assert!(
        v3.contains("pub value: u8"),
        "expected v3 to preserve the single field inside the nominal struct"
    );
}

#[test]
fn enum_constraints_compile_in_v3() {
    let v3 = compile_v3_from_rel(&["test", "src", "enum_constraints.vest"]);

    assert!(
        v3.contains("Refined<MyEnumCombinator, fn(MyEnum) -> bool>"),
        "expected enum-constrained fields to refine the named enum combinator",
    );
    assert!(
        v3.contains("matches!(v, MyEnum::A | MyEnum::C)"),
        "expected set enum constraints to lower to enum-pattern predicates",
    );
    assert!(
        v3.contains("matches!(v, MyTypedEnum::X)"),
        "expected typed enum constraints to lower to typed enum-pattern predicates",
    );
}
