// Copyright 2020 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use anyhow::{bail, Context, Error};
use fehler::throws;
use libtest_mimic::{run_tests, Arguments, Outcome, Test};
use std::fs::{read_dir, read_to_string};
use std::path::Path;
use wasmbin::{
    io::DecodeError,
    visit::{Visit, VisitError},
    Module,
};
use wast::parser::{parse, ParseBuffer};
use wast::Wast;

const IGNORED_ERRORS: &[&str] = &[
    // We don't perform cross-section analysis.
    "function and code section have inconsistent lengths",
    "data count section required",
    "data count and data section have inconsistent lengths",
    // We allow non-zero table and memory IDs already.
    "zero flag expected",
    // We don't perform full function analysis either.
    "too many locals",
];

const IGNORED_MODULES: &[&[u8]] = &[
    // These are outdated tests in WebAssembly/testsuite itself.
    // It needs updating, but see https://github.com/WebAssembly/testsuite/pull/39#issuecomment-863496809.
    &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x05, 0x03, 0x01, 0x00, 0x00, 0x0B, 0x07,
        0x01, 0x80, 0x00, 0x41, 0x00, 0x0B, 0x00,
    ],
    &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x04, 0x04, 0x01, 0x70, 0x00, 0x00, 0x09,
        0x07, 0x01, 0x80, 0x00, 0x41, 0x00, 0x0B, 0x00,
    ],
    &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x05, 0x03, 0x01, 0x00, 0x00, 0x0B, 0x06,
        0x01, 0x01, 0x41, 0x00, 0x0B, 0x00,
    ],
    &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x0B, 0x06, 0x01, 0x01, 0x41, 0x00, 0x0B,
        0x00,
    ],
    // Upstream malformed test that becomes well-formed if threads are enabled.
    #[cfg(feature = "threads")]
    &[
        0x00, 0x61, 0x73, 0x6D, 0x01, 0x00, 0x00, 0x00, 0x05, 0x03, 0x01, 0x02, 0x00,
    ],
];

struct WasmTest {
    module: Vec<u8>,
    expect_result: Result<(), String>,
}

#[throws]
fn read_tests_from_file(path: &Path, dest: &mut Vec<Test<WasmTest>>) {
    let src = read_to_string(path)?;
    let set_err_path_text = |mut err: wast::Error| {
        err.set_path(path);
        err.set_text(&src);
        err
    };
    let buf = ParseBuffer::new(&src).map_err(set_err_path_text)?;
    let wast = parse::<Wast>(&buf).map_err(set_err_path_text)?;
    for directive in wast.directives {
        let (span, mut module, expect_result) = match directive {
            // Expect errors for assert_malformed on binary or AST modules.
            wast::WastDirective::AssertMalformed {
                span,
                module: wast::QuoteModule::Module(module),
                message,
            }
            // Unlike other AssertInvalid, this is actually something we
            // check at the parsing time, because it's part of our
            // typesystem and doesn't require cross-function or
            // cross-section checks.
            //
            // See https://github.com/WebAssembly/simd/issues/256 for accepted
            // but pending suggestion to change proposal to match this as well.
            | wast::WastDirective::AssertInvalid {
                span,
                module,
                message: message @ "invalid lane index",
            } => (span, module, Err(message.to_owned())),
            // Expect successful parsing for regular AST modules.
            wast::WastDirective::Module(module) => (module.span, module, Ok(())),
            // Counter-intuitively, expect successful parsing for modules that are supposed
            // to error out at runtime or linking stage, too.
            wast::WastDirective::AssertInvalid { span, module, .. }
            | wast::WastDirective::AssertUnlinkable { span, module, .. } => (span, module, Ok(())),
            _ => {
                // Skipping interpreted
                continue;
            }
        };
        let (line, col) = span.linecol_in(&src);
        let module = module.encode()?;
        dest.push(Test {
            name: format!("{}:{}:{}", path.display(), line + 1, col + 1),
            kind: String::default(),
            is_ignored: IGNORED_MODULES.contains(&module.as_slice())
                || match &expect_result {
                    Ok(()) => false,
                    Err(err) => IGNORED_ERRORS.contains(&err.as_str()),
                },
            is_bench: false,
            data: WasmTest {
                module,
                expect_result,
            },
        });
    }
}

#[throws]
fn read_tests_from_dir(path: &Path, dest: &mut Vec<Test<WasmTest>>) {
    for file in read_dir(path)? {
        let path = file?.path();
        if path.extension().map_or(false, |ext| ext == "wast") {
            read_tests_from_file(&path, dest)?;
        }
    }
}

#[throws]
fn read_all_tests(path: &Path) -> Vec<Test<WasmTest>> {
    let mut tests = Vec::new();
    let proposals_dir = path.join("proposals");

    macro_rules! read_proposal_tests {
        ($name:literal) => {
            if cfg!(feature = $name) {
                read_tests_from_dir(&proposals_dir.join($name), &mut tests).context($name)?
            }
        };
    }

    read_proposal_tests!("tail-call");
    read_proposal_tests!("simd");
    read_proposal_tests!("threads");

    read_tests_from_dir(path, &mut tests)?;

    if tests.is_empty() {
        bail!("Couldn't find any tests. Did you run `git submodule update --init`?");
    }

    tests
}

fn unlazify<T: Visit>(mut wasm: T) -> Result<T, DecodeError> {
    match wasm.visit_mut(|()| {}) {
        Ok(()) => Ok(wasm),
        Err(err) => match err {
            VisitError::LazyDecode(err) => Err(err),
            VisitError::Custom(err) => match err {},
        },
    }
}

#[throws]
fn run_test(test: &WasmTest) {
    let module = match (Module::decode_from(&mut test.module.as_slice()).and_then(unlazify), &test.expect_result) {
        (Ok(ref module), Err(err)) => bail!("Expected an invalid module definition with an error: {}\nParsed part: {:02X?}\nGot module: {:02X?}", err, test.module, module),
        (Err(err), Ok(())) => bail!(
            "Expected a valid module definition, but got an error\nModule: {:02X?}\nError: {:#}",
            test.module,
            err
        ),
        (Ok(module), Ok(())) => module,
        (Err(_), Err(_)) => return,
    };
    let out = module.encode_into(Vec::new())?;
    if out != test.module {
        // In the rare case that binary representation doesn't match, it
        // might be because the test uses longer LEB128 form than
        // required. Verify that at least decoding it back produces the
        // same module.
        let module2 = Module::decode_from(out.as_slice())?;
        if module != module2 {
            bail!(
                "Roundtrip mismatch. Old: {:#?}\nNew: {:#?}",
                module,
                module2
            );
        }
    }
}

#[throws]
fn main() {
    let tests = read_all_tests(&Path::new("tests").join("testsuite"))?;

    run_tests(&Arguments::from_args(), tests, |test| {
        match run_test(&test.data) {
            Ok(()) => Outcome::Passed,
            Err(err) => Outcome::Failed {
                msg: Some(err.to_string()),
            },
        }
    })
    .exit_if_failed();
}
