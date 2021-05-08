/*

Demonstrates normalisation of coordinates.

Normalisation happens after coordinates are transformed.

*/

use prop::*;
use path_semantics::*;
use nat::*;

// Normalise corners from `2 1 2 0` to `0 1 2 2`.
pub fn proof<A: LProp<N = Zero>, B: LProp<N = One>, C: LProp<N = Two>, D: LProp<N = Two>>()
-> PSemNaive<A, B, C, D> {
    assume_norm_path_level::<C, B, D, A>()
}

fn main() {}
