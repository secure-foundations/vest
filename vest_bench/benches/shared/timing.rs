//! Timing policy shared by every benchmark. Output storage is prepared outside
//! timing; decoded values and freshly allocated encoder outputs are dropped after it.

use std::hint::black_box;
use std::path::Path;

use criterion::{BatchSize, Bencher, Criterion};

#[cfg(feature = "allocation-counting")]
#[path = "allocations.rs"]
mod allocations;

#[cfg(not(feature = "allocation-counting"))]
#[global_allocator]
static ALLOCATOR: std::alloc::System = std::alloc::System;

pub fn configuration() -> Criterion {
    assert!(
        !vest_lib::ERROR_TRACE_ENABLED,
        "benchmarks must not enable vest_lib/error-trace (including through workspace feature unification)"
    );
    #[cfg(feature = "allocation-counting")]
    assert!(
        std::env::args().any(|arg| arg == "--test"),
        "allocation-counting is an untimed audit; use --test, never --bench"
    );
    let mut criterion = Criterion::default();
    if let Some(path) = std::env::var_os("VEST_BENCH_CRITERION_DIR") {
        criterion = criterion.output_directory(Path::new(&path));
    }
    criterion
}

/// Retain one result per item until Criterion stops the timer. The common
/// outer result vector is allocated in setup, not by the codec under test.
/// PerIteration bounds memory even for multi-megabyte Bitcoin/CMS corpora.
pub fn retained<T>(b: &mut Bencher, count: usize, mut item: impl FnMut(usize) -> T) {
    #[cfg(feature = "allocation-counting")]
    {
        let mut outputs = Vec::with_capacity(count);
        allocations::record(|| {
            fill(&mut outputs, count, &mut item);
        });
        drop(outputs);
    }
    b.iter_batched_ref(
        || Vec::with_capacity(count),
        |outputs| {
            fill(outputs, count, &mut item);
            black_box(outputs);
        },
        BatchSize::PerIteration,
    );
}

pub(crate) fn fill<T>(outputs: &mut Vec<T>, count: usize, item: &mut impl FnMut(usize) -> T) {
    for i in 0..count {
        outputs.push(black_box(item(i)));
    }
}

/// Encoders with a timed exact-length calculation can reuse a destination.
pub fn reused(b: &mut Bencher, mut pass: impl FnMut()) {
    #[cfg(feature = "allocation-counting")]
    allocations::record(&mut pass);
    b.iter(&mut pass);
}

/// Criterion supports only one throughput unit; retain item counts separately
/// so microformat reports can show both byte throughput and latency per item.
pub fn corpus_metadata(group: &str, items: usize, bytes: u64) {
    if std::env::var("VEST_BENCH_JOB").is_ok_and(|job| job.starts_with(&format!("{group}/"))) {
        if let Some(path) = std::env::var_os("VEST_BENCH_METADATA_FILE") {
            let data = serde_json::json!({ "items": items, "bytes": bytes });
            std::fs::write(path, serde_json::to_vec(&data).unwrap()).unwrap();
        }
    }
}
