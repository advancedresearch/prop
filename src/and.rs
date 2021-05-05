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

/// `(¬a ∧ ¬b) => ¬(a ∨ b)`.
pub fn to_de_morgan<A: Prop, B: Prop>(
    (f0, f1): And<Not<A>, Not<B>>
) -> Not<Or<A, B>> {
    use Either::*;

    match (A::decide(), B::decide()) {
        (Left(a), _) => match f0(a) {},
        (_, Left(b)) => match f1(b) {},
        (Right(a), Right(b)) => Rc::new(move |x| match x {
            Left(xa) => a.clone()(xa),
            Right(xb) => b.clone()(xb),
        })
    }
}

/// `¬(a ∨ b) => (¬a ∧ ¬b)`.
pub fn from_de_morgan<A: Prop, B: Prop>(
    f: Not<Or<A, B>>
) -> And<Not<A>, Not<B>> {
    use Either::*;

    match (A::decide(), B::decide()) {
        (Left(a), _) => match f(Left(a)) {},
        (_, Left(b)) => match f(Right(b)) {},
        (Right(not_a), Right(not_b)) => (not_a, not_b),
    }
}

/// `(false ∧ a) => false`.
pub fn false_arg<A: Prop>((x, _): And<False, A>) -> False {x}

/// `(true ∧ a) => true`.
pub fn true_arg<A: Prop>((_, x): And<True, A>) -> A {x}

/// `(a ∧ b) ∧ (a => c)  =>  (c ∧ b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(
    (x, y): And<A, B>, g: Imply<A, C>
) -> And<C, B> {
    (g(x), y)
}

/// `(a ∧ b) ∧ (b => c)  =>  (a ∧ c)`.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(
    (x, y): And<A, B>, g: Imply<B, C>
) -> And<A, C> {
    (x, g(y))
}

/// `¬(a => b)  =>  (a ∧ ¬b)`.
pub fn from_imply<A: Prop, B: Prop>(f: Not<Imply<A, B>>) -> And<A, Not<B>> {
    // `(¬a ∨ b)  =>  (a => b)`
    let f2 = Rc::new(move |x| imply::from_or(x));
    // `¬(¬a ∨ b)`
    let g = imply::rev_modus_ponens(f2, f);
    // `¬¬a ∧ ¬b`
    let h = from_de_morgan(g);
    and::in_left_arg(h, Rc::new(move |x| not::rev_double(x)))
}
