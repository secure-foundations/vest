// Use vest's Pair/SpecPair instead of custom Depend implementation
// This provides type aliases for backward compatibility with existing code

use super::*;
use vstd::prelude::*;

verus! {

/// Type alias: SpecDepend is now vest's SpecPair
/// SpecPair<Fst, Snd> = Pair<Fst, Snd, GhostFn<<Fst as SpecCombinator>::Type, Snd>>
/// where GhostFn = spec_fn(Input) -> Output
pub type SpecDepend<Fst, Snd> = SpecPair<Fst, Snd>;

/// Type alias: Depend is now vest's Pair
/// Pair<Fst, Snd, Cont> where Cont implements Continuation trait
pub type Depend<Fst, Snd, Cont> = Pair<Fst, Snd, Cont>;

}
