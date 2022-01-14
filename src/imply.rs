//! Tactics for Logical IMPLY.

use crate::*;

/// `a => b  =>  ¬b => ¬a`.
///
/// Swap sides of implication by taking their negation.
pub fn modus_tollens<A: Prop, B: Prop>(f: Imply<A, B>) -> Imply<Not<B>, Not<A>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    })
}

/// `¬b => ¬a  =>  a => b`.
pub fn rev_modus_tollens<A: DProp, B: DProp>(f: Imply<Not<B>, Not<A>>) -> Imply<A, B> {
    imply::rev_double_neg(Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    }))
}

/// `a => b ∧ b => c  =>  a => c`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    f: Imply<A, B>,
    g: Imply<B, C>,
) -> Imply<A, C> {
    Rc::new(move |x| g(f(x)))
}

/// `(a => b) ∧ a  =>  b`
pub fn modus_ponens<A: Prop, B: Prop>(
    f: Imply<A, B>,
    a: A,
) -> B {
    f(a)
}

/// `(b => a) ∧ ¬a  => ¬b`.
pub fn rev_modus_ponens<A: Prop, B: DProp>(g: Imply<B, A>, f: Not<A>) -> Not<B> {
    modus_tollens(g)(f)
}

/// `a => (b => c)  =>  b => (a => c)`
pub fn reorder_args<A: Prop, B: Prop, C: Prop>(
    f: Imply<A, Imply<B, C>>
) -> Imply<B, Imply<A, C>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| f(y)(x.clone()))
    })
}

/// `(a => b)  =>  ¬¬a => ¬¬b`.
pub fn double_neg<A: DProp, B: Prop>(f: Imply<A, B>) -> Imply<Not<Not<A>>, Not<Not<B>>> {
    Rc::new(move |nn_a| not::double(f(not::rev_double(nn_a))))
}

/// `(¬¬a => ¬¬b)  =>  a => b`.
pub fn rev_double_neg<A: DProp, B: DProp>(f: Imply<Not<Not<A>>, Not<Not<B>>>) -> Imply<A, B> {
    use Either::*;

    let a = <A as Decidable>::decide();
    let b = <B as Decidable>::decide();
    match (a, b) {
        (_, Left(b)) => b.map_any(),
        (Right(a), _) => Rc::new(move |x| match a(x) {}),
        (Left(a), Right(b)) => match f(not::double(a))(b) {}
    }
}

/// `(a => b) => (¬a ∨ b)`.
pub fn to_or<A: DProp, B: DProp>(f: Imply<A, B>) -> Or<Not<A>, B> {
    use Either::*;

    let a = <A as Decidable>::decide();
    let b = <B as Decidable>::decide();
    match (a, b) {
        (_, Left(b)) => Right(b),
        (Left(a), _) => Right(f(a)),
        (Right(a), _) => Left(a.clone()),
    }
}

/// `(¬a ∨ b) => (a => b)`.
pub fn from_or<A: DProp, B: DProp>(f: Or<Not<A>, B>) -> Imply<A, B> {
    use Either::*;

    let a = <A as Decidable>::decide();
    let b = <B as Decidable>::decide();
    match (a, b) {
        (_, Left(b)) => b.map_any(),
        (Left(a), _) => match f {
            Left(x) => match x(a) {},
            Right(b) => b.map_any(),
        }
        (Right(a), _) => Rc::new(move |x| match a(x) {}),
    }
}

/// `(¬a => b) => (¬b => a)`.
pub fn flip_neg_left<A: DProp, B: Prop>(f: Imply<Not<A>, B>) -> Imply<Not<B>, A> {
    let g = imply::modus_tollens(f);
    Rc::new(move |x| not::rev_double(g(x)))
}

/// `(a => ¬b) => (b => ¬a)`.
pub fn flip_neg_right<A: Prop, B: Prop>(f: Imply<A, Not<B>>) -> Imply<B, Not<A>> {
    let g = imply::modus_tollens(f);
    Rc::new(move |x| g(not::double(x)))
}

/// `((a ∧ b) => c  =>  a => (b => c))`.
pub fn chain<A: Prop, B: Prop, C: Prop>(
    f: Imply<And<A, B>, C>
) -> Imply<A, Imply<B, C>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| f((x.clone(), y)))
    })
}

/// `(a => b) ∧ (a = c)  =>  (c => b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(f: Imply<A, B>, (_, g1): Eq<A, C>) -> Imply<C, B> {
    transitivity(g1, f)
}

/// `(a => b) ∧ (b = c)  =>  (a => c)`.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(f: Imply<A, B>, (g0, _): Eq<B, C>) -> Imply<A, C> {
    transitivity(f, g0)
}

/// `(a => c) ∧ (b => c)  =>  ((a ∧ b) => c)`.
pub fn join<A: Prop, B: Prop, C: Prop>(f: Imply<A, C>, _: Imply<B, C>) -> Imply<And<A, B>, C> {
    Rc::new(move |(a, _)| f.clone()(a))
}

/// `false => a`.
pub fn absurd<A: Prop>() -> Imply<False, A> {
    Rc::new(|x| match x {})
}

/// `a => a`.
pub fn id<A: Prop>() -> Imply<A, A> {
    Rc::new(|x| x)
}
