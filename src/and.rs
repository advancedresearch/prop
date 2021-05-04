//! Tactics for Logical AND.

use crate::*;

/// `a ∧ b => b ∧ a`.
pub fn commute<A: Prop, B: Prop>((f0, f1): And<A, B>) -> And<B, A> {
    (f1, f0)
}

/// `(a ∧ b) ∧ c  =>  a ∧ (b ∧ c)`
pub fn assoc<A: Prop, B: Prop, C: Prop>(
    ((x0, x1), x2): And<And<A, B>, C>
) -> And<A, And<B, C>> {
    (x0, (x1, x2))
}

/// `a ∧ (b ∨ c)  =>  (a ∧ b) ∨ (a ∧ c)`
pub fn distrib<A: Prop, B: Prop, C: Prop>(
    (a, x): And<A, Or<B, C>>
) -> Or<And<A, B>, And<A, C>> {
    use Either::*;

    match x {
        Left(b) => Left((a, b)),
        Right(c) => Right((a, c)),
    }
}
