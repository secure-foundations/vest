pub use crate::utils::*;
// use core::rc::Rc;
use alloc::vec::Vec;

use vstd::prelude::*;
use vstd::slice::*;
use vstd::*;

verus! {

//////////////////////////////////////////////////////////////////////////////
/// Trait definitions
/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte buffers.
/// `VestInput` does not expose the contents of the buffer, so opaque buffer types for side-channel
/// security can implement `VestInput`.
pub trait VestInput: View<V = Seq<u8>> {
    /// The length of the buffer.
    fn len(&self) -> (res: usize)
        ensures
            res == self@.len(),
    ;

    /// Analogous to `vstd::slice_subrange`
    fn subrange(&self, i: usize, j: usize) -> (res: Self) where Self: Sized
        requires
            0 <= i <= j <= self@.len(),
        ensures
            res@ == self@.subrange(i as int, j as int),
    ;

    /// Creates another buffer with the same contents.
    /// For good performance, this function should be cheap, just creating a new reference rather than
    /// actually copying the buffer.
    fn clone(&self) -> (res: Self) where Self: Sized
        ensures
            res@ == self@,
    ;
}

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte buffers.
/// `VestPublicInput` can be set using transparent bytes, so it cannot provide type abstraction for side-channel security.
pub trait VestPublicInput: VestInput {
    /// Returns a byte slice with the contents of the buffer
    fn as_byte_slice(&self) -> (res: &[u8])
        ensures
            res@ == self@,
    ;
}

/// Trait for types that can be used as output for Vest serializers.
/// `VestOutput` does not expose the contents of the buffer, so opaque buffer types for side-channel
/// security can implement `VestOutput`.
pub trait VestOutput<I>: View<V = Seq<u8>> where I: View<V = Seq<u8>> {
    /// The length of the buffer.
    fn len(&self) -> (res: usize)
        ensures
            res == self@.len(),
    ;

    /// Copy `input` to `self` starting at index `i`.
    fn set_range(&mut self, i: usize, input: &I) -> (res: ())
        requires
            0 <= i + input@.len() <= old(self)@.len() <= usize::MAX,
        ensures
            self@.len() == old(self)@.len() && self@ == old(self)@.subrange(0, i as int).add(
                input@,
            ).add(old(self)@.subrange(i + input@.len(), self@.len() as int)),
    ;
}

/// Trait for types that can be used as output for Vest serializers.
/// `VestPublicOutput` can be set using transparent bytes, so it cannot provide type abstraction for side-channel security.
pub trait VestPublicOutput<I>: VestOutput<I> where I: View<V = Seq<u8>> {
    /// Set the byte at index `i` to `value`.
    fn set_byte(&mut self, i: usize, value: u8)
        requires
            i < old(self)@.len(),
        ensures
            self@ == old(self)@.update(i as int, value),
    ;

    /// Copy `input` to `self` starting at index `i`. (Same as `set_range` but with byte slice input.)
    fn set_byte_range(&mut self, i: usize, input: &[u8]) -> (res: ())
        requires
            0 <= i + input@.len() <= old(self)@.len() <= usize::MAX,
        ensures
            self@.len() == old(self)@.len() && self@ == old(self)@.subrange(0, i as int).add(
                input@,
            ).add(old(self)@.subrange(i + input@.len(), self@.len() as int)),
    ;
}

//////////////////////////////////////////////////////////////////////////////
/// Implementations for common types
impl<'a> VestInput for &'a [u8] {
    fn len(&self) -> usize {
        <[u8]>::len(self)
    }

    fn subrange(&self, i: usize, j: usize) -> &'a [u8] {
        slice_subrange(*self, i, j)
    }

    fn clone(&self) -> &'a [u8] {
        *self
    }
}

impl<'a> VestPublicInput for &'a [u8] {
    fn as_byte_slice(&self) -> &[u8] {
        *self
    }
}

// /// Provided to demonstrate flexibility of the trait, but likely should not be used,
// /// since this impl copies the `Vec` every time you call `subrange` or `clone`.
// impl VestSecretInput for Vec<u8> {
//     fn len(&self) -> usize {
//         Vec::len(self)
//     }
//     fn subrange(&self, i: usize, j: usize) -> Vec<u8> {
//         let mut res = Vec::new();
//         vec_u8_extend_from_slice(&mut res, slice_subrange(self.as_slice(), i, j));
//         proof {
//             assert_seqs_equal!(res@, self@.subrange(i as int, j as int));
//         }
//         res
//     }
//     fn clone(&self) -> Vec<u8> {
//         Clone::clone(self)
//     }
// }
// impl VestInput for Vec<u8> {
//     fn as_byte_slice(&self) -> &[u8] {
//         self.as_slice()
//     }
// }
// /// Provided to demonstrate flexibility of the trait, but likely should not be used,
// /// since this impl copies the `Vec` every time you call `subrange` or `clone`.
// impl VestSecretInput for Rc<Vec<u8>> {
//     fn len(&self) -> usize {
//         Vec::len(self)
//     }
//     fn subrange(&self, i: usize, j: usize) -> Rc<Vec<u8>> {
//         let mut res = Vec::new();
//         vec_u8_extend_from_slice(&mut res, slice_subrange(self.as_slice(), i, j));
//         proof {
//             assert_seqs_equal!(res@, self@.subrange(i as int, j as int));
//         }
//         Rc::new(res)
//     }
//     fn clone(&self) -> Rc<Vec<u8>> {
//         Clone::clone(self)
//     }
// }
// impl VestInput for Rc<Vec<u8>> {
//     fn as_byte_slice(&self) -> &[u8] {
//         self.as_slice()
//     }
// }
impl<I> VestOutput<I> for Vec<u8> where I: VestPublicInput {
    fn len(&self) -> usize {
        Vec::len(self)
    }

    fn set_range(&mut self, i: usize, input: &I) {
        set_range(self, i, input.as_byte_slice());
    }
}

impl<I> VestPublicOutput<I> for Vec<u8> where I: VestPublicInput {
    fn set_byte(&mut self, i: usize, value: u8) {
        self.set(i, value);
    }

    fn set_byte_range(&mut self, i: usize, input: &[u8]) {
        set_range(self, i, input);
    }
}

} // verus!
