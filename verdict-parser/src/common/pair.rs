use super::*;
/// Use a custom pair type so that we can impl traits on it
use vstd::prelude::*;

verus! {

#[derive(Debug, View, PolyfillClone)]
pub struct PairValue<T1, T2>(pub T1, pub T2);


}
