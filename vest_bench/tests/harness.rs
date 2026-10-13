use criterion::Criterion;
use std::{cell::Cell, rc::Rc, time::Duration};
use vest_bench::harness::Group;

#[test]
fn retained_results_survive_the_whole_pass() {
    struct Live(Rc<Cell<usize>>);
    impl Drop for Live {
        fn drop(&mut self) {
            self.0.set(self.0.get() - 1);
        }
    }
    let live = Rc::new(Cell::new(0));
    let directory = std::env::temp_dir().join(format!("vest-bench-harness-{}", std::process::id()));
    let mut criterion = Criterion::default()
        .without_plots()
        .nresamples(100)
        .sample_size(10)
        .warm_up_time(Duration::from_millis(1))
        .measurement_time(Duration::from_millis(1))
        .output_directory(&directory);
    let mut group = Group::new(&mut criterion, "test/retained/parse", 3, 3);
    group.retained("test", |i| {
        assert_eq!(live.get(), i);
        live.set(i + 1);
        Live(Rc::clone(&live))
    });
    group.finish();
    assert_eq!(live.get(), 0);
    std::fs::remove_dir_all(directory).unwrap();
}
