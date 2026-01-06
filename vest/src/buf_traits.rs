use alloc::vec::Vec;

/// Trait for types that can be used as input for Vest parsers, roughly corresponding to byte
/// buffers.
pub trait VestInput {
    /// The length of the buffer.
    fn len(&self) -> usize;

    /// A slice-like view of the range `[i, j)`.
    fn subrange(&self, i: usize, j: usize) -> &Self;

    /// A slice-like view of the first `n` bytes.
    fn take(&self, n: usize) -> &Self {
        self.subrange(0, n)
    }

    /// A slice-like view of the buffer with the first `n` bytes skipped.
    fn skip(&self, n: usize) -> &Self {
        self.subrange(n, self.len())
    }
}

/// Trait for public inputs that can expose their underlying bytes.
pub trait VestPublicInput: VestInput {
    /// Returns a byte slice with the contents of the buffer.
    fn as_byte_slice(&self) -> &[u8];
}

/// Trait for types that can be used as output for Vest serializers.
pub trait VestOutput<I: ?Sized> {
    /// The length of the buffer.
    fn len(&self) -> usize;

    /// Copy `input` to `self` starting at index `i`.
    fn set_range(&mut self, i: usize, input: &I);
}

/// Trait for outputs that can be directly modified byte-by-byte.
pub trait VestPublicOutput<I: ?Sized>: VestOutput<I> {
    /// Set the byte at index `i` to `value`.
    fn set_byte(&mut self, i: usize, value: u8);

    /// Copy `input` to `self` starting at index `i`. (Same as `set_range` but with byte slice input.)
    fn set_byte_range(&mut self, i: usize, input: &[u8]);
}

impl VestInput for [u8] {
    fn len(&self) -> usize {
        (*self).len()
    }

    fn subrange(&self, i: usize, j: usize) -> &Self {
        &self[i..j]
    }
}

impl VestPublicInput for [u8] {
    fn as_byte_slice(&self) -> &[u8] {
        self
    }
}

impl<I> VestOutput<I> for Vec<u8>
where
    I: VestPublicInput + ?Sized,
{
    fn len(&self) -> usize {
        self.len()
    }

    fn set_range(&mut self, i: usize, input: &I) {
        let bytes = input.as_byte_slice();
        assert!(i <= self.len(), "set_range start out of bounds");
        assert!(
            i + bytes.len() <= self.len(),
            "set_range would write past end of buffer"
        );
        self[i..i + bytes.len()].copy_from_slice(bytes);
    }
}

impl<I> VestPublicOutput<I> for Vec<u8>
where
    I: VestPublicInput + ?Sized,
{
    fn set_byte(&mut self, i: usize, value: u8) {
        assert!(i < self.len(), "set_byte out of bounds");
        self[i] = value;
    }

    fn set_byte_range(&mut self, i: usize, input: &[u8]) {
        assert!(i <= self.len(), "set_byte_range start out of bounds");
        assert!(
            i + input.len() <= self.len(),
            "set_byte_range would write past end of buffer"
        );
        self[i..i + input.len()].copy_from_slice(input);
    }
}
