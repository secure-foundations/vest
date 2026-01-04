extern crate alloc;

use alloc::vec::Vec;

/// A helper trait for comparing values of potentially different types.
pub trait Compare<Other> {
    /// Compare a value of `Self` with a value of `Other`.
    fn compare(&self, other: &Other) -> bool;
}

impl<'a, 'b> Compare<&'b [u8]> for &'a [u8] {
    fn compare(&self, other: &&'b [u8]) -> bool {
        compare_slice(self, *other)
    }
}

/// Helper function to set a range of bytes in a vector.
pub fn set_range(data: &mut Vec<u8>, i: usize, input: &[u8]) {
    assert!(i <= data.len(), "set_range start out of bounds");
    assert!(
        i + input.len() <= data.len(),
        "set_range would write past end of buffer"
    );
    data[i..i + input.len()].copy_from_slice(input);
}

/// Helper function to compare two slices.
pub fn compare_slice(x: &[u8], y: &[u8]) -> bool {
    x == y
}
