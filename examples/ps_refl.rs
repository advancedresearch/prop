/*

Demonstrates that assuming `<A, A, A, A>` is same as `A = A`.

*/

use prop::*;
use path_semantics::*;

/// This proof shows that one can prove `A = A` with
/// a safe assumption using the core axiom.
pub fn proof_1<A: LProp>() -> Eq<A, A>
    // Try comment the next line to trigger an error.
    where A::N: nat::Lt<A::N>
{
    let p = assume_naive::<A, A, A, A>();
    p((eq::refl(), (imply::id(), imply::id())))
}

/// Here is a shorter proof, which is equivalent to the first one.
pub fn proof_2<A: LProp>() -> Eq<A, A> {
    eq::refl()
}

fn main() {}
