//! Vest and hand-written codecs with matching value shapes and wire behavior.
use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;
use vest_bench::{
    check_wire_compat, for_each_microformat,
    harness::Group,
    micro::{encode, Corpus},
};
use vest_lib::core::exec::Parser;

macro_rules! bench_micro {
    ($($format:ident),* $(,)?) => {
        fn bench(c: &mut Criterion) {
            let corpus = Corpus::new();
            $({
                use vest_bench::micro::$format as m;
                let values = m::values(&corpus);
                let inputs: Vec<_> = values.iter().map(|v| encode(&m::Format, v)).collect();
                let hand = check_wire_compat!(m, &values, &inputs);
                let bytes = inputs.iter().map(|b| b.len() as u64).sum();
                let id = concat!("micro/", stringify!($format));
                let mut group = Group::new(c, format!("{id}/parse"), inputs.len(), bytes);
                group.retained("Vest", |i| m::Format.parse(black_box(&inputs[i].as_slice())).unwrap());
                group.retained("hand-written", |i| m::parse(black_box(&inputs[i])).unwrap());
                group.finish();
                let mut output = vec![0; inputs.iter().map(Vec::len).max().unwrap()];
                let mut group = Group::serializing(c, format!("{id}/serialize"), &m::Format, &values);
                group.reused("hand-written", || {
                    for value in &hand {
                        let n = m::size(black_box(value)).unwrap();
                        m::write(black_box(value), black_box(&mut output[..n]));
                        black_box(&output[..n]);
                    }
                });
                group.finish();
            })*
        }
    };
}
for_each_microformat!(bench_micro);
criterion_group! { name = benches; config = vest_bench::harness::criterion(); targets = bench }
criterion_main!(benches);
