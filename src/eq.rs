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
pub fn imply_to_or<A: DProp, B: DProp>() -> Eq<Imply<A, B>, Or<Not<A>, B>> {
    (Rc::new(move |x| imply::to_or(x)), Rc::new(move |x| imply::from_or(x)))
}

/// `a = a`.
pub fn refl<A: Prop>() -> Eq<A, A> {
    (Rc::new(move |x| x), Rc::new(move |x| x))
}

/// `(a = b) = (¬a = ¬b)`
pub fn modus_tollens<A: Prop, B: Prop>((f0, f1): Eq<A, B>) -> Eq<Not<B>, Not<A>> {
    let f02 = imply::modus_tollens(f0);
    let f12 = imply::modus_tollens(f1);
    (f02, f12)
}

/// `(¬a = ¬b) = (a = b)`
pub fn rev_modus_tollens<A: DProp, B: DProp>((f0, f1): Eq<Not<A>, Not<B>>) -> Eq<B, A> {
    let f02 = imply::rev_modus_tollens(f0);
    let f12 = imply::rev_modus_tollens(f1);
    (f02, f12)
}

/// `(true = a) => a`.
pub fn is_true<A: Prop>((f0, _): Eq<True, A>) -> A {
    f0(True)
}

/// `(false = a) => ¬a`.
pub fn is_false<A: Prop>((_, f1): Eq<False, A>) -> Not<A> {
    f1
}

/// `¬(a = b) ∧ a  =>  ¬b`.
pub fn contra<A: DProp, B: DProp>(f: Not<Eq<A, B>>, a: A) -> Not<B> {
    match (A::decide(), B::decide()) {
        (Left(a), Left(b)) => match f(and::to_eq_pos((a, b))) {},
        (_, Right(not_b)) => not_b,
        (Right(not_a), _) => match not_a(a) {},
    }
}

/// `(a = b) = c  =>  a => (b = c)`
pub fn assoc_right<A: DProp, B: DProp, C: DProp>((f0, f1): Eq<Eq<A, B>, C>) -> Imply<A, Eq<B, C>> {
    match (A::decide(), C::decide()) {
        (Right(not_a), _) => Rc::new(move |x| match not_a.clone()(x) {}),
        (_, Left(c)) =>
            Rc::new(move |x| (c.clone().map_any(), f1.clone()(c.clone()).0(x).map_any())),
        (Left(a), Right(not_c)) => {
            // `!(a = b)`
            let g = imply::rev_modus_ponens(f0, not_c.clone());
            let not_b = eq::contra(g, a);
            and::to_eq_neg((not_b, not_c)).map_any()
        }
    }
}

/// `(a = b) = c  =>  (b = c) => a`.
pub fn assoc_left<A: DProp, B: DProp, C: DProp>((f0, f1): Eq<Eq<A, B>, C>) -> Imply<Eq<B, C>, A> {
    match (A::decide(), B::decide(), C::decide()) {
        (Left(a), _, _) => a.map_any(),
        (Right(not_a), Right(not_b), Right(not_c)) =>
            match not_c(f0(and::to_eq_neg((not_a, not_b)))) {},
        (_, Left(b), Right(not_c)) =>
            Rc::new(move |(fb, _)| match not_c.clone()(fb(b.clone())) {}),
        (_, Right(not_b), Left(c)) =>
            Rc::new(move |(_, fc)| match not_b.clone()(fc(c.clone())) {}),
        (Right(not_a), Left(b), Left(c)) => {
            // `a = b`.
            let (_, g1) = f1(c);
            let a = g1(b);
            match not_a(a) {}
        }
    }
}

/// `(a = b) = c  =>  a = (b = c)`.
pub fn assoc<A: DProp, B: DProp, C: DProp>(f: Eq<Eq<A, B>, C>) -> Eq<A, Eq<B, C>> {
    (assoc_right(f.clone()), assoc_left(f))
}

/// `a = (b = c)  =>  a = (c = b)`.
pub fn swap_right<A: DProp, B: Prop, C: Prop>((f0, f1): Eq<A, Eq<B, C>>) -> Eq<A, Eq<C, B>> {
    (Rc::new(move |x| {let (g0, g1) = f0(x); (g1, g0)}),
     Rc::new(move |(g1, g0)| f1((g0, g1))))
}

/// `(a = b) = c  =>  (b = a) = c`.
pub fn swap_left<A: DProp, B: Prop, C: DProp>(f: Eq<Eq<A, B>, C>) -> Eq<Eq<B, A>, C> {
    commute(swap_right(commute(f)))
}

/// `(a = b) ∧ (a = c)  =>  (c = b)`
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(f: Eq<A, B>, g: Eq<A, C>) -> Eq<C, B> {
    commute(transitivity(commute(f), g))
}

/// See transitivity.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(f: Eq<A, B>, g: Eq<B, C>) -> Eq<A, C> {
    transitivity(f, g)
}

/// `(a = b) = (b = a)`.
pub fn commute_eq<A: Prop, B: Prop>() -> Eq<Eq<A, B>, Eq<B, A>> {
    (Rc::new(move |x| eq::commute(x)),
     Rc::new(move |x| eq::commute(x)))
}
