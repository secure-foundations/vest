//! Common timing policy: prepare inside timing, retain results until it stops.

use criterion::{measurement::WallTime, BatchSize, BenchmarkGroup, Criterion, Throughput};
use std::hint::black_box;
use std::io::Write;
use vest_lib::core::exec::{output::OutputSlice, Parser, Prepare, Serializer, SerializerExt};
use vstd::prelude::DeepView;

const _: () = assert!(
    !vest_lib::ERROR_TRACE_ENABLED,
    "benchmarks must not enable vest_lib/error-trace"
);

pub fn criterion() -> Criterion {
    #[cfg(feature = "allocation-counting")]
    assert!(
        std::env::args().any(|arg| arg == "--test"),
        "allocation-counting is an untimed audit; use --test"
    );
    Criterion::default()
}

/// Registration and corpus metadata, with the timing modes shared by all targets.
pub struct Group<'a> {
    inner: BenchmarkGroup<'a, WallTime>,
    id: String,
    items: usize,
    bytes: u64,
}

impl<'a> Group<'a> {
    pub fn new(c: &'a mut Criterion, id: impl Into<String>, items: usize, bytes: u64) -> Self {
        assert!(items > 0, "a benchmark corpus must not be empty");
        let id = id.into();
        assert_eq!(
            id.split('/').count(),
            3,
            "group IDs are family/workload/operation"
        );
        let mut inner = c.benchmark_group(&id);
        inner.throughput(Throughput::Bytes(bytes));
        Self {
            inner,
            id,
            items,
            bytes,
        }
    }

    fn register(&self, implementation: &str) -> String {
        assert!(!implementation.contains('/'));
        let id = format!("{}/{implementation}", self.id);
        if let Some(path) = std::env::var_os("VEST_BENCH_INVENTORY") {
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .unwrap();
            writeln!(
                file,
                "{}",
                serde_json::json!({"id": id, "items": self.items, "bytes": self.bytes})
            )
            .unwrap();
        }
        id
    }

    /// Retain one result per item. Result storage and destruction are untimed.
    pub fn retained<T>(&mut self, implementation: &str, mut item: impl FnMut(usize) -> T) {
        let count = self.items;
        let _id = self.register(implementation);
        self.inner.bench_function(implementation, |b| {
            let mut pass = |outputs: &mut Vec<T>| {
                for i in 0..count {
                    outputs.push(black_box(item(i)));
                }
                black_box(outputs);
            };
            #[cfg(feature = "allocation-counting")]
            {
                let mut outputs = Vec::with_capacity(count);
                crate::allocations::record(&_id, || pass(&mut outputs));
            }
            b.iter_batched_ref(
                || Vec::with_capacity(count),
                &mut pass,
                BatchSize::PerIteration,
            );
        });
    }

    /// Encoders with a timed exact-length calculation can reuse their destination.
    pub fn reused(&mut self, implementation: &str, mut pass: impl FnMut()) {
        let _id = self.register(implementation);
        self.inner.bench_function(implementation, |b| {
            #[cfg(feature = "allocation-counting")]
            crate::allocations::record(&_id, &mut pass);
            b.iter(&mut pass);
        });
    }

    /// Derive output size, allocate the slice, and register Vest's serializer.
    pub fn serializing<F, T>(
        c: &'a mut Criterion,
        id: impl Into<String>,
        fmt: &F,
        values: &[T],
    ) -> Self
    where
        F: Prepare<T> + SerializerExt<T> + for<'b> Serializer<OutputSlice<'b>, T>,
        T: DeepView,
    {
        let (bytes, capacity) = values
            .iter()
            .map(|v| fmt.prepare(v).unwrap())
            .fold((0u64, 0usize), |(bytes, capacity), n| {
                (bytes + n as u64, capacity.max(n))
            });
        let mut group = Self::new(c, id, values.len(), bytes);
        let mut output = vec![0; capacity];
        group.reused("Vest", || {
            for value in values {
                let n = fmt.prepare(black_box(value)).unwrap();
                fmt.serialize(black_box(value), black_box(&mut output[..n]));
                black_box(&output[..n]);
            }
        });
        group
    }

    pub fn finish(self) {
        self.inner.finish();
    }
}

/// Full consumption without requiring the parser's encoding to be canonical.
pub fn parse_complete<'i, F: Parser<&'i [u8]>>(fmt: &F, input: &'i [u8]) -> Result<F::PT, String> {
    let (n, value) = fmt
        .parse(&input)
        .map_err(|error| format!("rejected: {error}"))?;
    if n != input.len() {
        return Err(format!("consumed {n} of {} bytes", input.len()));
    }
    Ok(value)
}

/// Byte-preserving workloads only; BER/CBOR alternatives use semantic checks.
pub fn roundtrip<'i, F>(fmt: &F, input: &'i [u8]) -> Result<F::PT, String>
where
    F: Parser<&'i [u8]> + Prepare<F::PT> + for<'b> Serializer<OutputSlice<'b>, F::PT>,
{
    let value = parse_complete(fmt, input)?;
    let mut output = vec![
        0;
        fmt.prepare(&value)
            .map_err(|error| format!("prepare failed: {error:?}"))?
    ];
    fmt.serialize(&value, &mut output);
    if output != input {
        return Err("serialized bytes differ".to_owned());
    }
    Ok(value)
}
