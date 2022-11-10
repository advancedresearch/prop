/*

This example proves some cases of `hooo::hooo_dual_and` without using it.

The motivation is to establish when `hooo::hooo_dual_and` can be trusted.

*/

use std::rc::Rc;

use prop::*;
use hooo::*;
use Either::*;

fn main() {}

/// `(c^(a ⋀ b) ⋀ a^true ⋀ b^true) => (c^a ⋁ c^b)`.
pub fn hooo_dual_and_tauto_tauto<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, And<A, B>>,
    tauto_a: Tauto<A>,
    tauto_b: Tauto<B>
) -> Or<Pow<C, A>, Pow<C, B>> {
    fn f<A: Prop>(_: True) -> Eq<And<True, A>, A> {
        (Rc::new(move |and_true_a| and_true_a.1), Rc::new(move |a| (True, a)))
    }
    let tauto_and_ab = hooo_rev_and((tauto_a, tauto_b));
    let x = pow_transitivity(tauto_and_ab, x);
    let x: Pow<C, And<True, A>> = pow_lower(pow_lift(x));
    Left(pow_in_right_arg(x, f))
}

/// `(c^(a ⋀ b) ⋀ (false^a ⋁ false^b)) => (c^a ⋁ c^b)`.
pub fn hooo_dual_and_para<A: Prop, B: Prop, C: Prop>(
    _x: Pow<C, And<A, B>>,
    _tauto_a: Tauto<A>,
    y: Or<Para<A>, Para<B>>
) -> Or<Pow<C, A>, Pow<C, B>> {
    match y {
        Left(y) => Left(pow_transitivity(y, fa())),
        Right(y) => Right(pow_transitivity(y, fa())),
    }
}
