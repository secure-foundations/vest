//! Separate, untimed System-allocator audit. Never enabled in timing binaries.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

#[derive(Clone, Copy, Default, serde::Serialize)]
struct Counts {
    allocations: u64,
    reallocations: u64,
    requested_bytes: u64,
    deallocations: u64,
}

thread_local! {
    static COUNTS: Cell<Option<Counts>> = const { Cell::new(None) };
}

struct CountingSystem;
#[global_allocator]
static ALLOCATOR: CountingSystem = CountingSystem;

fn update(f: impl FnOnce(&mut Counts)) {
    let _ = COUNTS.try_with(|cell| {
        if let Some(mut counts) = cell.get() {
            f(&mut counts);
            cell.set(Some(counts));
        }
    });
}

unsafe impl GlobalAlloc for CountingSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc(layout) };
        if !ptr.is_null() {
            update(|c| {
                c.allocations += 1;
                c.requested_bytes += layout.size() as u64;
            });
        }
        ptr
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = unsafe { System.alloc_zeroed(layout) };
        if !ptr.is_null() {
            update(|c| {
                c.allocations += 1;
                c.requested_bytes += layout.size() as u64;
            });
        }
        ptr
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        update(|c| c.deallocations += 1);
        unsafe { System.dealloc(ptr, layout) };
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let ptr = unsafe { System.realloc(ptr, layout, size) };
        if !ptr.is_null() {
            update(|c| {
                c.reallocations += 1;
                c.requested_bytes += size as u64;
            });
        }
        ptr
    }
}

pub(crate) fn record(id: &str, f: impl FnOnce()) {
    // Disable counting on unwinding as well as on successful completion.
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            COUNTS.with(|c| c.set(None));
        }
    }
    COUNTS.with(|c| c.set(Some(Counts::default())));
    let reset = Reset;
    f();
    let counts = COUNTS.with(|c| c.get().unwrap());
    drop(reset);
    if let Some(path) = std::env::var_os("VEST_BENCH_ALLOCATIONS") {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();
        let mut entry = serde_json::to_value(counts).unwrap();
        entry["id"] = serde_json::Value::String(id.to_owned());
        writeln!(file, "{entry}").unwrap();
    }
}
