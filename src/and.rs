//! Tactics for Logical AND.

#![allow(unreachable_code)]

use crate::*;

pub use commute as symmetry;

/// `a ∧ b => b ∧ a`.
pub fn commute<A: Prop, B: Prop>((f0, f1): And<A, B>) -> And<B, A> {
    (f1, f0)
}

/// `(a ∧ b) ∧ c  =>  a ∧ (b ∧ c)`.
pub fn assoc<A: Prop, B: Prop, C: Prop>(
    ((x0, x1), x2): And<And<A, B>, C>
) -> And<A, And<B, C>> {
    (x0, (x1, x2))
}

/// `a ∧ (b ∨ c)  =>  (a ∧ b) ∨ (a ∧ c)`.
pub fn distrib<A: Prop, B: Prop, C: Prop>(
    (a, x): And<A, Or<B, C>>
) -> Or<And<A, B>, And<A, C>> {
    match x {
        Left(b) => Left((a, b)),
        Right(c) => Right((a, c)),
    }
}

/// `¬a ∧ (a ∨ b)  =>  b`.
pub fn exc_left<A: Prop, B: Prop>((not_a, x): And<Not<A>, Or<A, B>>) -> B {
    match x {
        Left(a) => match not_a(a) {},
        Right(b) => b
    }
}

/// `¬b ∧ (a ∨ b)  =>  a`
pub fn exc_right<A: Prop, B: Prop>(
    (not_b, x): And<Not<B>, Or<A, B>>
) -> A {
    match x {
        Left(a) => a,
        Right(b) => match not_b(b) {},
    }
}

/// `(¬a ∧ ¬b) ∧ (a ∨ b)  =>  a`
pub fn exc_both<A: Prop, B: Prop>(
    ((not_a, not_b), x): And<And<Not<A>, Not<B>>, Or<A, B>>
) -> False {
    match x {
        Left(a) => match not_a(a) {},
        Right(b) => match not_b(b) {},
    }
}

/// `(¬a ∧ ¬b) => ¬(a ∨ b)`.
pub fn to_de_morgan<A: Prop, B: Prop>((f0, f1): And<Not<A>, Not<B>>) -> Not<Or<A, B>> {
    Rc::new(move |or_ab| match or_ab {
        Left(a) => match f0(a) {},
        Right(b) => match f1(b) {},
    })
}

/// `¬(a ∨ b) => (¬a ∧ ¬b)`.
pub fn from_de_morgan<A: Prop, B: Prop>(f: Not<Or<A, B>>) -> And<Not<A>, Not<B>> {
    let f2 = f.clone();
    (
        Rc::new(move |a| f(Left(a))),
        Rc::new(move |b| f2(Right(b))),
    )
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
pub fn from_imply<A: DProp, B: DProp>(f: Not<Imply<A, B>>) -> And<A, Not<B>> {
    // `(¬a ∨ b)  =>  (a => b)`
    let f2 = Rc::new(move |x| imply::from_or(x));
    // `¬(¬a ∨ b)`
    let g = imply::rev_modus_ponens(f2, f);
    // `¬¬a ∧ ¬b`
    let h = from_de_morgan(g);
    and::in_left_arg(h, Rc::new(move |x| not::rev_double(x)))
}

/// `(a ∧ ¬b)  =>  ¬(a => b)`.
pub fn to_imply<A: DProp, B: DProp>(f: And<A, Not<B>>) -> Not<Imply<A, B>> {
    // `(¬¬a ∧ ¬b)`
    let g: And<Not<Not<A>>, Not<B>> = and::in_left_arg(f, Rc::new(move |x| not::double(x)));
    // `¬(¬a ∨ b)`
    let h: Not<Or<Not<A>, B>> = and::to_de_morgan(g);
    // `(a => b)  =>  (¬a ∨ b)`
    let h2: Imply<Imply<A, B>, Or<Not<A>, B>> = Rc::new(move |x| imply::to_or(x));
    // `¬(a => b)`
    imply::rev_modus_ponens(h2, h)
}

/// `(a ∧ b) => (a = b)`.
pub fn to_eq_pos<A: Prop, B: Prop>((f0, f1): And<A, B>) -> Eq<A, B> {
    (f1.map_any(), f0.map_any())
}

/// `(¬a ∧ ¬b) => (a = b)`.
pub fn to_eq_neg<A: Prop, B: Prop>((f0, f1): And<Not<A>, Not<B>>) -> Eq<A, B> {
    (Rc::new(move |x| match f0.clone()(x) {}), Rc::new(move |x| match f1.clone()(x) {}))
}
