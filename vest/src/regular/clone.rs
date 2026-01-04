use super::bytes::{Fixed, Tail, Variable};
use super::uints::{U16Le, U32Le, U64Le, U8};

impl Clone for U8 {
    fn clone(&self) -> Self {
        U8
    }
}

impl Clone for U16Le {
    fn clone(&self) -> Self {
        U16Le
    }
}

impl Clone for U32Le {
    fn clone(&self) -> Self {
        U32Le
    }
}

impl Clone for U64Le {
    fn clone(&self) -> Self {
        U64Le
    }
}

impl Clone for Tail {
    fn clone(&self) -> Self {
        Tail
    }
}

impl Clone for Variable {
    fn clone(&self) -> Self {
        Variable(self.0)
    }
}

impl<const N: usize> Clone for Fixed<N> {
    fn clone(&self) -> Self {
        Fixed
    }
}
