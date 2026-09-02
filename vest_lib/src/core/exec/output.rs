//! Output abstractions for executable serializers.
#[cfg(feature = "alloc")]
use alloc::vec::Vec;
use vstd::prelude::*;

verus! {

/// An abstraction for append-oriented output buffer.
///
/// The view is the sequence already present in, or written through, the output. Capacity is
/// abstract: bounded and unbounded outputs expose the same `fits` interface.
pub trait OutputBuf: View<V = Seq<u8>> {
    /// Whether the output can accept `len` additional bytes.
    spec fn fits(&self, len: nat) -> bool;

    /// Write capacity is monotone: accepting a larger write implies accepting every prefix.
    broadcast proof fn lemma_fits_mono(&self, shorter: nat, longer: nat)
        requires
            shorter <= longer,
            self.fits(longer),
        ensures
            #![all_triggers]
            self.fits(shorter),
    ;

    /// Whether two states write to the same final destination.
    ///
    /// This is vacuously true for outputs without (re-)borrowed backing storage. For a borrowed
    /// output, it relates the prophetic final contents of the backing storage across states.
    #[verifier::prophetic]
    spec fn same_destination(&self, other: &Self) -> bool;

    /// Destination identity is reflexive.
    broadcast proof fn lemma_same_destination_reflexive(&self)
        ensures
            #[trigger] self.same_destination(self),
    ;

    /// Destination identity is transitive.
    broadcast proof fn lemma_same_destination_transitive(&self, middle: &Self, last: &Self)
        requires
            self.same_destination(middle),
            middle.same_destination(last),
        ensures
            #![all_triggers]
            self.same_destination(last),
    ;

    /// Appends one byte to the logical output.
    fn write_byte(&mut self, byte: u8)
        requires
            old(self).fits(1),
        ensures
            final(self)@ == old(self)@.push(byte),
            forall|n| old(self).fits(1 + n) <==> #[trigger] final(self).fits(n),
            old(self).same_destination(final(self)),
    ;

    /// Appends all bytes in `bytes` to the logical output.
    fn write_bytes(&mut self, bytes: &[u8])
        requires
            old(self).fits(bytes@.len()),
        ensures
            final(self)@ == old(self)@ + bytes@,
            forall|n| old(self).fits(bytes@.len() + n) <==> #[trigger] final(self).fits(n),
            old(self).same_destination(final(self)),
    {
        broadcast use OutputBuf::lemma_same_destination_reflexive;

        let ghost initial_view = self@;
        for i in 0..bytes.len()
            invariant
                self@ == initial_view + bytes@.take(i as int),
                old(self).fits(bytes@.len()),
                forall|n| old(self).fits(i as nat + n) <==> #[trigger] self.fits(n),
                old(self).same_destination(self),
        {
            broadcast use OutputBuf::lemma_same_destination_transitive;

            proof {
                old(self).lemma_fits_mono(i as nat + 1, bytes@.len());
                assert(self.fits(1));
            }
            self.write_byte(bytes[i]);
        }
    }
}

/// A non-allocating append sink backed by a caller-provided slice.
///
/// Its logical view is the prefix written so far (given by `pos`).
pub struct OutputSlice<'a> {
    pub obuf: &'a mut [u8],
    pub pos: usize,
}

impl View for OutputSlice<'_> {
    type V = Seq<u8>;

    open spec fn view(&self) -> Self::V {
        self.obuf@.take(self.pos as int)
    }
}

impl<'a> OutputSlice<'a> {
    /// The prophetic final contents of the caller-provided backing slice.
    #[verifier::prophetic]
    pub open spec fn final_destination(&self) -> Seq<u8> {
        final(self.obuf)@
    }

    /// Creates an empty logical output over `obuf` without allocating.
    pub fn new(obuf: &'a mut [u8]) -> (output: Self)
        ensures
            output@ == Seq::empty(),
            output.fits(old(obuf)@.len()),
            forall|len: nat| #[trigger] output.fits(len) == (len <= old(obuf)@.len()),
            output.final_destination() == final(obuf)@,
    {
        Self { obuf, pos: 0 }
    }
}

impl OutputBuf for OutputSlice<'_> {
    open spec fn fits(&self, len: nat) -> bool {
        self.pos as nat + len <= self.obuf@.len()
    }

    proof fn lemma_fits_mono(&self, shorter: nat, longer: nat) {
    }

    #[verifier::prophetic]
    open spec fn same_destination(&self, other: &Self) -> bool {
        self.final_destination() == other.final_destination()
    }

    proof fn lemma_same_destination_reflexive(&self) {
    }

    proof fn lemma_same_destination_transitive(&self, _middle: &Self, _last: &Self) {
    }

    fn write_byte(&mut self, byte: u8) {
        assert(self.pos < self.obuf.len());
        self.obuf[self.pos] = byte;
        self.pos += 1;
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        let ghost old_view = self@;
        let old_pos = self.pos;
        let len = bytes.len();
        assert(old_pos + len <= self.obuf.len());
        {
            let (_prefix, rest) = self.obuf.split_at_mut(old_pos);
            let (destination, _suffix) = rest.split_at_mut(len);
            destination.copy_from_slice(bytes);
        }
        self.pos = old_pos + len;
        assert(self@ == old_view + bytes@);
    }
}

#[cfg(feature = "alloc")]
impl OutputBuf for Vec<u8> {
    open spec fn fits(&self, _len: nat) -> bool {
        true
    }

    proof fn lemma_fits_mono(&self, _shorter: nat, _longer: nat) {
    }

    #[verifier::prophetic]
    open spec fn same_destination(&self, _other: &Self) -> bool {
        true
    }

    proof fn lemma_same_destination_reflexive(&self) {
    }

    proof fn lemma_same_destination_transitive(&self, _middle: &Self, _last: &Self) {
    }

    fn write_byte(&mut self, byte: u8) {
        self.push(byte);
    }

    fn write_bytes(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

pub broadcast group outbuf_lemmas {
    OutputBuf::lemma_fits_mono,
    OutputBuf::lemma_same_destination_reflexive,
    OutputBuf::lemma_same_destination_transitive,
}

} // verus!
