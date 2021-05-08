/*

This example demonstrates safely assumption of `<False, False, A, B>`.

When two symbols are not defined, their meaning is equal, but unknown.

*/

use prop::*;
use path_semantics::*;

/*
// Uncomment this to check that it is not possible to safely assume `<False, False, A, B>`.
pub fn proof_1<A: LProp, B: Prop>() -> Eq<A, B> {
    naive_red_false(assume_path_level::<False, False, A, B>())
}
*/

// By assuming `<False, False, A, B>`, one can prove that `A = B`.
// This means that symbols, that are not defined, mean the same thing.
// They mean the same thing in the sense that we do not know what they mean.
pub fn proof_2<A: Prop, B: Prop>(p: PSemNaive<False, False, A, B>) -> Eq<A, B> {
    naive_red_false(p)
}

fn main() {}
