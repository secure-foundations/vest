//! Input abstractions for executable parsers.
use vstd::{prelude::*, slice::slice_subrange};

verus! {

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte
/// buffers.
pub trait InputBuf: View<V = Seq<u8>> {
    /// The length of the buffer.
    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    ;

    /// A slice-like view of the range `[i, j)` of the buffer.
    fn subrange(&self, i: usize, j: usize) -> (sliced: &Self)
        requires
            0 <= i <= j <= self@.len(),
        ensures
            sliced@ == self@.subrange(i as int, j as int),
    ;

    /// A view of the first `n` bytes of the buffer.
    fn take(&self, n: usize) -> (taken: &Self)
        requires
            n <= self@.len(),
        ensures
            taken@ == self@.take(n as int),
    {
        self.subrange(0, n)
    }

    /// A view of the buffer with the first `n` bytes skipped.
    fn skip(&self, n: usize) -> (skipped: &Self)
        requires
            n <= self@.len(),
        ensures
            skipped@ == self@.skip(n as int),
    {
        self.subrange(n, self.len())
    }
}

impl InputBuf for [u8] {
    fn len(&self) -> (len: usize) {
        self.len()
    }

    fn subrange(&self, i: usize, j: usize) -> &Self {
        slice_subrange(self, i, j)
    }
}

} // verus!
