//! CMS phase diagnostics. Setup and final output destruction are untimed.
//! `write` uses cached lengths to isolate writing; only `total` matches the benchmark.

use std::hint::black_box;
use std::time::{Duration, Instant};

use der::{Decode, Encode};
use vest_asn1_tests::generated_cms;
use vest_lib::core::exec::{ByteLen, Parser, Prepare, SerializerExt};

#[path = "../benches/shared/cms.rs"]
#[allow(dead_code)]
mod cms;

struct Options {
    implementation: String,
    phase: String,
    workload: String,
    seconds: f64,
    ready: Option<std::path::PathBuf>,
}

impl Options {
    fn parse() -> Self {
        let mut args = std::env::args().skip(1);
        let mut options = Self {
            implementation: args
                .next()
                .expect("cms_profile <vest|rustcrypto|rasn> <phase> [options]"),
            phase: args
                .next()
                .expect("phase: prepare, length, write, or total"),
            workload: "real_signed_data".into(),
            seconds: 5.0,
            ready: None,
        };
        while let Some(arg) = args.next() {
            let value = args.next().expect("option needs a value");
            match arg.as_str() {
                "--seconds" => options.seconds = value.parse().expect("seconds"),
                "--workload" => options.workload = value,
                "--ready-file" => options.ready = Some(value.into()),
                _ => panic!("unknown option: {arg}"),
            }
        }
        assert!(options.seconds.is_finite() && options.seconds > 0.0);
        assert!(matches!(
            options.workload.as_str(),
            "content_info" | "real_signed_data"
        ));
        assert!(
            match options.implementation.as_str() {
                "vest" => matches!(
                    options.phase.as_str(),
                    "prepare" | "length" | "write" | "total"
                ),
                "rustcrypto" => matches!(options.phase.as_str(), "length" | "write" | "total"),
                "rasn" => options.phase == "total",
                _ => false,
            },
            "unsupported implementation/phase"
        );
        options
    }
}

fn measure(
    options: &Options,
    items: usize,
    bytes: usize,
    mut pass: impl FnMut(),
    mut dispose: impl FnMut(),
) {
    let warmup = Instant::now();
    while warmup.elapsed() < Duration::from_secs(1) {
        pass();
        dispose();
    }
    if let Some(path) = &options.ready {
        std::fs::write(path, std::process::id().to_string()).unwrap();
    }
    let start = Instant::now();
    let mut samples = Vec::new();
    while start.elapsed().as_secs_f64() < options.seconds {
        let timer = Instant::now();
        pass();
        samples.push(timer.elapsed().as_nanos() as f64);
        dispose();
    }
    samples.sort_by(f64::total_cmp);
    let median = samples[samples.len() / 2];
    println!(
        "{}",
        serde_json::json!({
            "implementation": options.implementation, "phase": options.phase,
            "workload": options.workload, "items": items, "bytes": bytes,
            "passes": samples.len(), "median_ns": median,
            "p05_ns": samples[samples.len() / 20], "p95_ns": samples[samples.len() * 19 / 20],
            "mib_per_second": bytes as f64 * 1e9 / median / 1048576.0,
            "seconds": options.seconds,
            "note": "phase diagnostic; percentiles are not confidence intervals; final outputs drop outside timing",
        })
    );
}

macro_rules! vest_phases {
    ($options:expr, $inputs:expr, $fmt:expr) => {{
        let values: Vec<_> = $inputs
            .iter()
            .map(|b| $fmt.parse(&b.as_slice()).unwrap().1)
            .collect();
        let lengths: Vec<_> = values.iter().map(|v| $fmt.prepare(v).unwrap()).collect();
        let bytes = lengths.iter().sum();
        let mut output = vec![0; *lengths.iter().max().unwrap()];
        for (i, value) in values.iter().enumerate() {
            $fmt.serialize(value, &mut output[..lengths[i]]);
            assert_eq!(&output[..lengths[i]], &$inputs[i]);
        }
        match $options.phase.as_str() {
            "prepare" => measure(
                $options,
                values.len(),
                bytes,
                || {
                    for v in &values {
                        black_box($fmt.prepare(black_box(v)).unwrap());
                    }
                },
                || {},
            ),
            "length" => measure(
                $options,
                values.len(),
                bytes,
                || {
                    for v in &values {
                        black_box($fmt.length(black_box(v)));
                    }
                },
                || {},
            ),
            "write" => measure(
                $options,
                values.len(),
                bytes,
                || {
                    for (v, n) in values.iter().zip(&lengths) {
                        $fmt.serialize(black_box(v), black_box(&mut output[..*n]));
                        black_box(&output[..*n]);
                    }
                },
                || {},
            ),
            "total" => measure(
                $options,
                values.len(),
                bytes,
                || {
                    for v in &values {
                        let n = $fmt.prepare(black_box(v)).unwrap();
                        $fmt.serialize(black_box(v), black_box(&mut output[..n]));
                        black_box(&output[..n]);
                    }
                },
                || {},
            ),
            _ => unreachable!(),
        }
    }};
}

fn rustcrypto_phases<T: for<'a> Decode<'a> + Encode>(options: &Options, inputs: &[Vec<u8>]) {
    let values: Vec<T> = inputs.iter().map(|b| T::from_ber(b).unwrap()).collect();
    let lengths: Vec<usize> = values
        .iter()
        .map(|v| usize::try_from(v.encoded_len().unwrap()).unwrap())
        .collect();
    let bytes = lengths.iter().sum();
    let mut output = vec![0; *lengths.iter().max().unwrap()];
    for (i, value) in values.iter().enumerate() {
        assert_eq!(value.encode_to_slice(&mut output).unwrap(), inputs[i]);
    }
    match options.phase.as_str() {
        "length" => measure(
            options,
            values.len(),
            bytes,
            || {
                for v in &values {
                    black_box(black_box(v).encoded_len().unwrap());
                }
            },
            || {},
        ),
        "write" => measure(
            options,
            values.len(),
            bytes,
            || {
                for (v, n) in values.iter().zip(&lengths) {
                    black_box(
                        black_box(v)
                            .encode_to_slice(black_box(&mut output[..*n]))
                            .unwrap(),
                    );
                }
            },
            || {},
        ),
        "total" => measure(
            options,
            values.len(),
            bytes,
            || {
                for v in &values {
                    let n = usize::try_from(black_box(v).encoded_len().unwrap()).unwrap();
                    black_box(v.encode_to_slice(black_box(&mut output[..n])).unwrap());
                }
            },
            || {},
        ),
        _ => unreachable!(),
    }
}

fn rasn_phases<T: rasn::Decode + rasn::Encode>(options: &Options, inputs: &[Vec<u8>]) {
    let values: Vec<T> = inputs.iter().map(|b| cms::rasn_exact(b)).collect();
    for (v, b) in values.iter().zip(inputs) {
        assert_eq!(rasn::der::encode(v).unwrap(), *b);
    }
    let outputs = std::cell::RefCell::new(Vec::with_capacity(values.len()));
    measure(
        options,
        values.len(),
        inputs.iter().map(Vec::len).sum(),
        || {
            let mut outputs = outputs.borrow_mut();
            for v in &values {
                outputs.push(black_box(rasn::der::encode(black_box(v)).unwrap()));
            }
        },
        || outputs.borrow_mut().clear(),
    );
}

fn main() {
    assert!(
        !vest_lib::ERROR_TRACE_ENABLED,
        "disable vest_lib/error-trace for profiling"
    );
    let options = Options::parse();
    let inputs = if options.workload == "content_info" {
        cms::synthetic_content_info()
    } else {
        cms::real_signed_data()
            .iter()
            .map(|b| cms::normalized_signed_data(b))
            .collect()
    };
    match (options.implementation.as_str(), options.workload.as_str()) {
        ("vest", "content_info") => {
            vest_phases!(&options, inputs, generated_cms::CONTENT_INFO::Fmt)
        }
        ("vest", _) => vest_phases!(&options, inputs, generated_cms::SIGNED_DATA::Fmt),
        ("rustcrypto", "content_info") => {
            rustcrypto_phases::<rustcrypto_cms::content_info::ContentInfo>(&options, &inputs)
        }
        ("rustcrypto", _) => {
            rustcrypto_phases::<rustcrypto_cms::signed_data::SignedData>(&options, &inputs)
        }
        ("rasn", "content_info") => rasn_phases::<rasn_cms::ContentInfo>(&options, &inputs),
        ("rasn", _) => rasn_phases::<rasn_cms::SignedData>(&options, &inputs),
        _ => unreachable!(),
    }
}
