//! Input abstractions for executable parsers.
use vstd::{prelude::*, slice::slice_subrange};

verus! {

pub trait InputSlice: View<V = Seq<u8>> + DeepView<V = Seq<u8>> {
    proof fn deep_view_eq_view(&self)
        ensures
            self.deep_view() == self@,
    ;
}

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte
/// buffers.
pub trait InputBuf: InputSlice + Sized {
    /// The length of the buffer.
    fn len(&self) -> (len: usize)
        ensures
            len == self@.len(),
    ;

    /// A slice-like view of the range `[i, j)` of the buffer.
    fn subrange(&self, i: usize, j: usize) -> (sliced: Self)
        requires
            0 <= i as int <= j as int <= self@.len(),
        ensures
            sliced@ == self@.subrange(i as int, j as int),
            sliced.deep_view() == sliced@,
    ;

    /// A view of the first `n` bytes of the buffer.
    fn take(&self, n: usize) -> (taken: Self)
        requires
            n as int <= self@.len(),
        ensures
            taken@ == self@.take(n as int),
            taken.deep_view() == taken@,
    {
        self.subrange(0, n)
    }

    /// A view of the buffer with the first `n` bytes skipped.
    fn skip(&self, n: usize) -> (skipped: Self)
        requires
            n as int <= self@.len(),
        ensures
            skipped@ == self@.skip(n as int),
            skipped.deep_view() == skipped@,
    {
        self.subrange(n, self.len())
    }
}

impl<'input> InputSlice for &'input [u8] {
    proof fn deep_view_eq_view(&self) {
        assert(self.deep_view() == self@);
    }
}

impl<'input> InputBuf for &'input [u8] {
    fn len(&self) -> (len: usize) {
        <[u8]>::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> &'input [u8] {
        let sliced = slice_subrange(self, i, j);
        proof {
            sliced.deep_view_eq_view();
        }
        sliced
    }
}

// pub trait InputBuf: View<V = Seq<u8>> {
//     type Slice<'input>: DeepView<V = Seq<u8>> where Self: 'input;
//     /// The length of the buffer.
//     fn len(&self) -> (len: usize)
//         ensures
//             len == self@.len(),
//     ;
//     /// A slice-like view of the range `[i, j)` of the buffer.
//     fn subrange<'input>(&'input self, i: usize, j: usize) -> (sliced: Self::Slice<'input>)
//         requires
//             0 <= i <= j <= self@.len(),
//         ensures
//             sliced@ == self@.subrange(i as int, j as int),
//     ;
//     /// A view of the first `n` bytes of the buffer.
//     fn take<'input>(&'input self, n: usize) -> (taken: Self::Slice<'input>)
//         requires
//             n <= self@.len(),
//         ensures
//             taken@ == self@.take(n as int),
//     {
//         self.subrange(0, n)
//     }
//     /// A view of the buffer with the first `n` bytes skipped.
//     fn skip<'input>(&'input self, n: usize) -> (skipped: Self::Slice<'input>)
//         requires
//             n <= self@.len(),
//         ensures
//             skipped@ == self@.skip(n as int),
//     {
//         self.subrange(n, self.len())
//     }
// }
// impl InputBuf for [u8] {
//     type Slice<'input> = &'input [u8];
//     fn len(&self) -> (len: usize) {
//         self.len()
//     }
//     #[verifier::external_body]
//     fn subrange<'input>(&'input self, i: usize, j: usize) -> Self::Slice<'input> {
//         &self[i..j]
//     }
// }
} // verus!
