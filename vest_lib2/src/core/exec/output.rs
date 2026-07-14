//! Output abstractions for executable serializers.
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// Updates a remaining-capacity value after writing `len` bytes.
pub open spec fn consume(remaining: Option<nat>, len: nat) -> Option<nat> {
    match remaining {
        Some(n) => if len <= n {
            Some((n - len) as nat)
        } else {
            arbitrary()
        },
        None => None,
    }
}

/// Whether `len` bytes fit in a remaining-capacity value.
pub open spec fn fit(remaining: Option<nat>, len: nat) -> bool {
    remaining matches Some(n) ==> len <= n
}

/// An append-oriented output buffer.
///
/// The view is the sequence already present in, or written through, the output. A `None`
/// remaining capacity denotes an unbounded growable output; `Some(n)` denotes a bounded output
/// with `n` bytes left.
pub trait OutputBuf: View<V = Seq<u8>> {
    /// Representation invariant for the output implementation.
    spec fn wf(&self) -> bool;

    /// Bytes that can still be written, or `None` for an unbounded output.
    spec fn remaining(&self) -> Option<nat>;

    /// The final fixed backing storage, when the output has one.
    ///
    /// This prophecy is `None` for growable outputs and remains stable across writes. It lets a
    /// generic serializer return ownership of a caller-provided slice with a precise final view.
    #[verifier::prophetic]
    spec fn final_target(&self) -> Option<Seq<u8>>;

    /// Appends one byte to the logical output.
    fn write_byte(&mut self, byte: u8)
        requires
            old(self).wf(),
            fit(old(self).remaining(), 1),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.push(byte),
            final(self).remaining() == consume(old(self).remaining(), 1),
            final(self).final_target() == old(self).final_target(),
    ;

    /// Appends all bytes in `bytes` to the logical output.
    fn write_bytes(&mut self, bytes: &[u8])
        requires
            old(self).wf(),
            fit(old(self).remaining(), bytes@.len()),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@ + bytes@,
            final(self).remaining() == consume(old(self).remaining(), bytes@.len()),
            final(self).final_target() == old(self).final_target(),
    {
        let ghost initial_view = self@;
        let ghost initial_remaining = self.remaining();
        for i in 0..bytes.len()
            invariant
                self.wf(),
                self@ == initial_view + bytes@.take(i as int),
                self.remaining() == consume(initial_remaining, i as nat),
                fit(initial_remaining, bytes@.len()),
                self.final_target() == old(self).final_target(),
        {
            self.write_byte(bytes[i]);
        }
    }
}

/// A non-allocating append sink backed by a caller-provided slice.
///
/// Its logical view is the prefix written so far. The backing slice is fully populated when
/// `remaining()` is `Some(0)`.
pub struct OutputSlice<'a> {
    #[doc(hidden)]
    pub obuf: &'a mut [u8],
    #[doc(hidden)]
    pub pos: usize,
}

impl View for OutputSlice<'_> {
    type V = Seq<u8>;

    open spec fn view(&self) -> Self::V {
        self.obuf@.take(self.pos as int)
    }
}

impl<'a> OutputSlice<'a> {
    /// Creates an empty logical output over `obuf` without allocating.
    pub fn new(obuf: &'a mut [u8]) -> (output: Self)
        ensures
            output.wf(),
            output@ == Seq::empty(),
            output.remaining() == Some(old(obuf)@.len()),
            output.final_target() == Some(final(obuf)@),
    {
        Self { obuf, pos: 0 }
    }

    /// The complete current contents of the backing slice.
    pub open spec fn backing_view(&self) -> Seq<u8> {
        self.obuf@
    }
}

impl OutputBuf for OutputSlice<'_> {
    open spec fn wf(&self) -> bool {
        self.pos <= self.obuf@.len()
    }

    open spec fn remaining(&self) -> Option<nat> {
        Some((self.obuf@.len() - self.pos as int) as nat)
    }

    #[verifier::prophetic]
    open spec fn final_target(&self) -> Option<Seq<u8>> {
        Some(final(self.obuf)@)
    }

    fn write_byte(&mut self, byte: u8) {
        assert(self.pos < self.obuf.len());
        self.obuf[self.pos] = byte;
        self.pos += 1;
    }
}

impl OutputBuf for Vec<u8> {
    open spec fn wf(&self) -> bool {
        true
    }

    open spec fn remaining(&self) -> Option<nat> {
        None
    }

    #[verifier::prophetic]
    open spec fn final_target(&self) -> Option<Seq<u8>> {
        None
    }

    fn write_byte(&mut self, byte: u8) {
        self.push(byte);
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

} // verus!
