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

use std::fs::File;
use std::io::{BufReader, Seek, SeekFrom};
use structopt::StructOpt;
use wasmbin::io::DecodeError;
use wasmbin::sections::{Kind, Section};
use wasmbin::visit::{Visit, VisitError};
use wasmbin::Module;

#[derive(StructOpt)]
enum DumpSection {
    All,
    Custom { name: String },
    Type,
    Import,
    Function,
    Table,
    Memory,
    Global,
    Export,
    Start,
    Element,
    DataCount,
    Code,
    Data,
}

#[derive(StructOpt)]
struct DumpOpts {
    filename: String,
    #[structopt(long)]
    include_raw: bool,
    #[structopt(flatten)]
    section: DumpSection,
}

fn unlazify_with_opt<T: Visit>(wasm: &mut T, include_raw: bool) -> Result<(), DecodeError> {
    let res = if include_raw {
        wasm.visit(|()| {})
    } else {
        wasm.visit_mut(|()| {})
    };
    match res {
        Ok(()) => Ok(()),
        Err(err) => match err {
            VisitError::LazyDecode(err) => Err(err),
            VisitError::Custom(err) => match err {},
        },
    }
}

fn main() {
    let opts = DumpOpts::from_args();
    let f = File::open(opts.filename).unwrap();
    let mut f = BufReader::new(f);
    let mut m = Module::decode_from(&mut f).unwrap_or_else(|err| {
        panic!(
            "Parsing error at offset 0x{:08X}: {}",
            f.seek(SeekFrom::Current(0)).unwrap(),
            err
        )
    });
    let filter: Box<dyn Fn(&Section) -> bool> = match opts.section {
        DumpSection::All => Box::new(|_s: &Section| true) as _,
        DumpSection::Custom { name } => Box::new(move |s: &Section| {
            let other_name = match s {
                Section::Custom(s) => match s.try_contents() {
                    Ok(section) => Some(section.name()),
                    Err(err) => {
                        eprintln!("Warning: could not parse a custom section. {}", err);
                        None
                    }
                },
                _ => None,
            };
            Some(name.as_str()) == other_name
        }),
        DumpSection::Type => Box::new(|s| s.kind() == Kind::Type),
        DumpSection::Import => Box::new(|s| s.kind() == Kind::Import),
        DumpSection::Function => Box::new(|s| s.kind() == Kind::Function),
        DumpSection::Table => Box::new(|s| s.kind() == Kind::Table),
        DumpSection::Memory => Box::new(|s| s.kind() == Kind::Memory),
        DumpSection::Global => Box::new(|s| s.kind() == Kind::Global),
        DumpSection::Export => Box::new(|s| s.kind() == Kind::Export),
        DumpSection::Start => Box::new(|s| s.kind() == Kind::Start),
        DumpSection::Element => Box::new(|s| s.kind() == Kind::Element),
        DumpSection::DataCount => Box::new(|s| s.kind() == Kind::DataCount),
        DumpSection::Code => Box::new(|s| s.kind() == Kind::Code),
        DumpSection::Data => Box::new(|s| s.kind() == Kind::Data),
    };
    let mut count = 0;
    for s in m.sections.iter_mut().filter(|s| filter(s)) {
        count += 1;
        unlazify_with_opt(s, opts.include_raw).unwrap();
        println!("{:#?}", s);
    }
    println!("Found {} sections.", count);
}
