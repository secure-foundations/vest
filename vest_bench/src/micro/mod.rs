//! Deterministic test data shared by the benchmarks and the wire-compatibility
//! tests.
//!
//! The corpus owns byte storage; each format's `values` function borrows it.

/// Element counts, kept in one place so the harness and the tests agree.
const TABLE_COUNT: usize = 1_000;
const TABLE_ENTRIES: usize = 10;
const NEST_COUNT: usize = 10_000;
const BITS_COUNT: usize = 20_000;
const ADDRESS_COUNT: usize = 10_000;
const LIST_COUNT: usize = 5_000;
const LIST_ITEMS: usize = 12;

/// Reproducible LCG, so every run measures the same bytes.
struct Rng(u32);

impl Rng {
    fn next(&mut self, modulus: u32) -> u32 {
        self.0 = self.0.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
        (self.0 >> 8) % modulus
    }
}

/// Owned backing storage for every format's test data.
pub struct Corpus {
    entry_keys: Vec<[u8; 32]>,
    entry_values: Vec<Vec<u8>>,
    nest_payloads: Vec<Vec<u8>>,
    addrs: Vec<[u8; 4]>,
    list_bodies: Vec<Vec<u8>>,
}

impl Default for Corpus {
    fn default() -> Self {
        Self::new()
    }
}

impl Corpus {
    pub fn new() -> Self {
        // Independent seeds preserve the existing corpora without generating
        // removed workloads or coupling their random streams to each other.
        let mut table_rng = Rng(0xf0d1_8bc8);
        let total_entries = TABLE_COUNT * TABLE_ENTRIES;
        let entry_keys = (0..total_entries).map(|i| [i as u8; 32]).collect();
        let entry_values = (0..total_entries)
            .map(|_| vec![0xcd; (16 + table_rng.next(112)) as usize])
            .collect();

        let nest_payloads = (0..NEST_COUNT).map(|_| vec![0xef; 128]).collect();
        let addrs = (0..ADDRESS_COUNT)
            .map(|i| [10, 0, (i >> 8) as u8, i as u8])
            .collect();

        let mut list_rng = Rng(0xb85e_a368);
        let list_bodies = (0..LIST_COUNT * LIST_ITEMS)
            .map(|_| vec![0x33; (1 + list_rng.next(48)) as usize])
            .collect();
        Self {
            entry_keys,
            entry_values,
            nest_payloads,
            addrs,
            list_bodies,
        }
    }
}

/// Apply one callback to the microformat registry.
#[macro_export]
macro_rules! for_each_microformat {
    ($callback:ident) => {
        $callback!(table, nest, bits, bounded_list);
    };
}

macro_rules! declare {
    ($($name:ident),* $(,)?) => { $(pub mod $name;)* };
}
for_each_microformat!(declare);

const fn same_layout<V, H>() {
    assert!(core::mem::size_of::<V>() == core::mem::size_of::<H>());
    assert!(core::mem::align_of::<V>() == core::mem::align_of::<H>());
}

/// Encode a fixture once, outside benchmark timing.
pub fn encode<F, T>(fmt: &F, value: &T) -> Vec<u8>
where
    F: vest_lib::core::exec::Prepare<T>
        + vest_lib::core::exec::SerializerExt<T>
        + vest_lib::core::exec::Serializer<Vec<u8>, T>,
    T: vstd::prelude::DeepView + ?Sized,
{
    let mut output = Vec::new();
    fmt.serialize_with_vec(value, &mut output);
    output
}

/// Check both codecs on the same bytes, returning hand-written serializer values.
#[macro_export]
macro_rules! check_wire_compat {
    ($module:ident, $values:expr, $inputs:expr) => {{
        assert_eq!($values.len(), $inputs.len());
        let mut hand = Vec::with_capacity($inputs.len());
        for (value, input) in $values.iter().zip($inputs) {
            $crate::harness::roundtrip(&$module::Format, input).expect("Vest roundtrip failed");
            assert_eq!($crate::micro::encode(&$module::Format, value), *input);
            let (n, parsed) = $module::parse(input).expect("hand-written parse failed");
            assert_eq!(n, input.len());
            let n = $module::size(&parsed).expect("hand-written sizing rejected a valid value");
            assert_eq!(n, input.len());
            let mut output = vec![0; n];
            $module::write(&parsed, &mut output);
            assert_eq!(output, *input, "hand-written encoding differs");
            hand.push(parsed);
        }
        hand
    }};
}
