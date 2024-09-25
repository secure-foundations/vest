/// Builder combinator
pub mod builder;
/// Bytes combinator
pub mod bytes;
/// BytesN combinator
pub mod bytes_n;
/// OrdChoice combinator
pub mod choice;
/// Cond combinator
pub mod cond;
/// Mapped combinator
pub mod map;
/// Pair combinator
pub mod pair;
/// Refined combinator
pub mod refined;
// pub mod preser;
// mod repeat_n;
// mod repeat_n_const;
/// AndThen combinator
pub mod and_then;
/// impl Clone for some combinators
pub mod clone;
/// Depend combinator
pub mod depend;
// pub mod dependent;
/// Disjointness for OrdChoice combinator
pub mod disjoint;
/// Preceded combinator
pub mod preceded;
/// Tag combinator
pub mod tag;
/// Tail combinator
pub mod tail;
/// Uints combinator
pub mod uints;
/// Repeat combinator
pub mod repeat;
/// Error combinator
pub mod fail;
