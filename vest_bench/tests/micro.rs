//! Every registered microformat must agree with its hand-written codec.
use vest_bench::{
    check_wire_compat, for_each_microformat,
    micro::{encode, Corpus},
};

macro_rules! checks {
    ($($format:ident),* $(,)?) => {
        $(#[test]
        fn $format() {
            use vest_bench::micro::$format as m;
            let corpus = Corpus::new();
            let values = m::values(&corpus);
            let inputs: Vec<_> = values.iter().map(|value| encode(&m::Format, value)).collect();
            check_wire_compat!(m, &values, &inputs);
        })*
    };
}
for_each_microformat!(checks);
