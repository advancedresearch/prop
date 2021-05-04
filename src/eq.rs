//! Tactics for Logical EQ.

use crate::*;

/// `(a = b) ∧ (b = c) => (a = c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>((f0, f1): Eq<A, B>, (g0, g1): Eq<B, C>) -> Eq<A, C> {
    (Rc::new(move |x| g0(f0(x))), Rc::new(move |x| f1(g1(x))))
}

/// `a => (a = ¬¬a)`.
pub fn double_neg<A: Prop>(a: A) -> Eq<A, Not<Not<A>>> {
    let double_neg = a.double_neg();
    (Rc::new(move |x| not::double(x)), Rc::new(move |x| double_neg(x)))
}

/// `(a = b) => (b = a)`.
pub fn commute<A: Prop, B: Prop>((f0, f1): Eq<A, B>) -> Eq<B, A> {
    (f1, f0)
}

/// `(a => b) = (¬a ∨ b)`.
pub fn imply_to_or<A: Prop, B: Prop>() -> Eq<Imply<A, B>, Or<Not<A>, B>> {
    (Rc::new(move |x| imply::to_or(x)), Rc::new(move |x| imply::from_or(x)))
}

/// `a = a`.
pub fn refl<A: Prop>() -> Eq<A, A> {
    (Rc::new(move |x| x), Rc::new(move |x| x))
}
