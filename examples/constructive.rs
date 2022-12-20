/*

It is desirable to be able to predict whether a theorem
is constructive or not using composition of theorems:

    x : [constructive] true, y : [constructive] true
    ------------------------------------------------
    (x, y) : [constructive] true

In general, one would like to have normal paths, such as:

    and[constructive] <=> and

However, in order to do this prediction safely,
one must prove that the operation is safe for these predictions.

This safety property is proved using excluded middle for the tautology of some proposition:

    x^true | !(x^true)

This means, either we know `x` is constructive or non-constructive.

*/

use prop::*;
use std::rc::Rc;
use prop::Either::*;
use prop::hooo::*;

fn main() {
}

pub type Safe<A> = ExcM<Tauto<A>>;

pub fn and_is_safe<A: Prop, B: Prop>(
    safe_a: Safe<A>,
    safe_b: Safe<B>
) -> Safe<And<A, B>> {
    match (safe_a, safe_b) {
        (Left(tauto_a), Left(tauto_b)) => Left(tauto_and(tauto_a, tauto_b)),
        (Right(n_tauto_a), _) => Right(Rc::new(move |tauto_ab| {
            n_tauto_a(tauto_rev_and(tauto_ab).0)
        })),
        (_, Right(n_tauto_b)) => Right(Rc::new(move |tauto_ab| {
            n_tauto_b(tauto_rev_and(tauto_ab).1)
        }))
    }
}

pub fn or_is_safe<A: Prop, B: Prop>(
    safe_a: Safe<A>,
    safe_b: Safe<B>
) -> Safe<Or<A, B>> {
    match (safe_a, safe_b) {
        (Left(tauto_a), _) => Left(tauto_or_left(tauto_a)),
        (_, Left(tauto_b)) => Left(tauto_or_right(tauto_b)),
        (Right(n_tauto_a), Right(n_tauto_b)) => Right(Rc::new(move |tauto_or_ab| {
            match tauto_rev_or(tauto_or_ab) {
                Left(tauto_a) => n_tauto_a(tauto_a),
                Right(tauto_b) => n_tauto_b(tauto_b),
            }
        }))
    }
}

pub fn not_is_safe<A: DProp>(
    safe_a: Safe<A>
) -> Safe<Not<A>> {
    match safe_a {
        Left(tauto_a) => Right(tauto_rev_not(tauto_not_double(tauto_a))),
        Right(n_tauto_a) => Left(tauto_not(n_tauto_a)),
    }
}
