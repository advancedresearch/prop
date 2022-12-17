//! Tactics for Logical IMPLY.

#![allow(unreachable_code)]

use crate::*;

/// `(a => b)  =>  (¬b => ¬a)`.
///
/// Swap sides of implication by taking their negation.
pub fn modus_tollens<A: Prop, B: Prop>(f: Imply<A, B>) -> Imply<Not<B>, Not<A>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    })
}

/// `(¬b => ¬a)  =>  (a => b)`.
pub fn rev_modus_tollens<A: DProp, B: DProp>(f: Imply<Not<B>, Not<A>>) -> Imply<A, B> {
    imply::rev_double_neg(Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    }))
}

/// `(¬b => ¬a) ∧ (a ∨ ¬a) ∧ (b ∨ ¬b)  =>  (a => b)`.
pub fn rev_modus_tollens_excm<A: Prop, B: Prop>(
    f: Imply<Not<B>, Not<A>>,
    excm_a: ExcM<A>,
    excm_b: ExcM<B>,
) -> Imply<A, B> {
    imply::rev_double_neg_excm(Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    }), excm_a, excm_b)
}

/// `(¬b => ¬a) ∧ ((a ∨ ¬a) == (b ∨ ¬b))  =>  (a => b)`.
pub fn rev_modus_tollens_eq_excm<A: Prop, B: Prop>(
    f: Imply<Not<B>, Not<A>>,
    eq_excm_a_excm_b: Eq<ExcM<A>, ExcM<B>>,
) -> Imply<A, B> {
    imply::rev_double_neg_eq_excm(Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    }), eq_excm_a_excm_b)
}

/// `(¬b => ¬a) ∧ (a => (b ∨ ¬b))  =>  (a => b)`.
pub fn rev_modus_tollens_imply_excm<A: Prop, B: Prop>(
    f: Imply<Not<B>, Not<A>>,
    a_excm_b: Imply<A, ExcM<B>>,
) -> Imply<A, B> {
    imply::rev_double_neg_imply_excm(Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    }), a_excm_b)
}

/// `(a => b) ∧ (b => c)  =>  (a => c)`.
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
pub fn rev_modus_ponens<A: Prop, B: Prop>(g: Imply<B, A>, f: Not<A>) -> Not<B> {
    Rc::new(move |b| f(g(b)))
}

/// `(a => (b => c))  =>  (b => (a => c))`
pub fn reorder_args<A: Prop, B: Prop, C: Prop>(
    f: Imply<A, Imply<B, C>>
) -> Imply<B, Imply<A, C>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| f(y)(x.clone()))
    })
}

/// `(a => b)  =>  (¬¬a => ¬¬b)`.
pub fn double_neg<A: DProp, B: Prop>(f: Imply<A, B>) -> Imply<Not<Not<A>>, Not<Not<B>>> {
    Rc::new(move |nn_a| not::double(f(not::rev_double(nn_a))))
}

/// `(¬¬a => ¬¬b)  =>  (a => b)`.
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

/// `(¬¬a => ¬¬b)  =>  (a => b)`.
pub fn rev_double_neg_excm<A: Prop, B: Prop>(
    f: Imply<Not<Not<A>>, Not<Not<B>>>,
    excm_a: ExcM<A>,
    excm_b: ExcM<B>,
) -> Imply<A, B> {
    use Either::*;

    match (excm_a, excm_b) {
        (_, Left(b)) => b.map_any(),
        (Right(a), _) => Rc::new(move |x| match a(x) {}),
        (Left(a), Right(b)) => match f(not::double(a))(b) {}
    }
}

/// `(¬¬a => ¬¬b) ∧ ((a ∨ ¬a) == (b ∨ ¬b))  =>  (a => b)`.
pub fn rev_double_neg_eq_excm<A: Prop, B: Prop>(
    f: Imply<Not<Not<A>>, Not<Not<B>>>,
    eq_excm_a_excm_b: Eq<ExcM<A>, ExcM<B>>,
) -> Imply<A, B> {
    use Either::*;

    Rc::new(move |a| {
        match eq_excm_a_excm_b.0(Left(a.clone())) {
            Left(b) => b,
            Right(nb) => match f(not::double(a))(nb) {}
        }
    })
}

/// `(¬¬a => ¬¬b) ∧ (a => (b ∨ ¬b))  =>  (a => b)`.
pub fn rev_double_neg_imply_excm<A: Prop, B: Prop>(
    f: Imply<Not<Not<A>>, Not<Not<B>>>,
    a_excm_b: Imply<A, ExcM<B>>,
) -> Imply<A, B> {
    use Either::*;

    Rc::new(move |a| {
        match a_excm_b(a.clone()) {
            Left(b) => b,
            Right(nb) => match f(not::double(a))(nb) {}
        }
    })
}

/// `(a => b) => (¬a ∨ b)`.
pub fn to_or_da<A: DProp, B: Prop>(f: Imply<A, B>) -> Or<Not<A>, B> {
    use Either::*;

    match <A as Decidable>::decide() {
        Left(a) => Right(f(a)),
        Right(a) => Left(a.clone()),
    }
}

/// `(a => b) => (¬a ∨ b)`.
pub fn to_or_db<A: Prop, B: DProp>(f: Imply<A, B>) -> Or<Not<A>, B> {
    use Either::*;

    match <B as Decidable>::decide() {
        Left(b) => Right(b),
        Right(nb) => Left(modus_tollens(f)(nb)),
    }
}

/// `(¬a ∨ b) => (a => b)`.
pub fn from_or<A: Prop, B: Prop>(f: Or<Not<A>, B>) -> Imply<A, B> {
    Rc::new(move |a| {
        match f.clone() {
            Left(na) => absurd()(na(a)),
            Right(b) => b,
        }
    })
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

/// `((a ∧ b) => c)  =>  (a => (b => c))`.
pub fn chain<A: Prop, B: Prop, C: Prop>(
    f: Imply<And<A, B>, C>
) -> Imply<A, Imply<B, C>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| f((x.clone(), y)))
    })
}

/// `(a => b) ∧ (a == c)  =>  (c => b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(f: Imply<A, B>, (_, g1): Eq<A, C>) -> Imply<C, B> {
    transitivity(g1, f)
}

/// `(a => b) ∧ (b == c)  =>  (a => c)`.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(f: Imply<A, B>, (g0, _): Eq<B, C>) -> Imply<A, C> {
    transitivity(f, g0)
}

/// Makes it easier to traverse.
pub fn in_left<A: Prop, B: Prop, C: Prop, F>(
    ab: Imply<A, B>,
    f: F
) -> Imply<C, B>
    where F: Fn(C) -> A + 'static
{
    Rc::new(move |c| ab(f(c)))
}

/// Makes it easier to traverse.
pub fn in_right<A: Prop, B: Prop, C: Prop, F>(
    ab: Imply<A, B>,
    f: F
) -> Imply<A, C>
    where F: Fn(A, B) -> C + 'static
{
    Rc::new(move |a| f(a.clone(), ab(a)))
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

/// `(a => (b ∨ c))  =>  (a => b) ∨ (a => c)`.
pub fn or_split_da<A: DProp, B: Prop, C: Prop>(
    f: Imply<A, Or<B, C>>
) -> Or<Imply<A, B>, Imply<A, C>> {
    match A::decide() {
        Left(a) => match f(a) {
            Left(b) => Left(b.map_any()),
            Right(c) => Right(c.map_any())
        }
        Right(na) => Left(Rc::new(move |a| not::absurd(na.clone(), a)))
    }
}

/// `(a => (b ∨ c))  =>  (a => b) ∨ (a => c)`.
pub fn or_split_db<A: Prop, B: DProp, C: Prop>(
    f: Imply<A, Or<B, C>>
) -> Or<Imply<A, B>, Imply<A, C>> {
    match B::decide() {
        Left(b) => Left(b.map_any()),
        Right(nb) => Right(Rc::new(move |a| match f(a) {
            Left(b) => not::absurd(nb.clone(), b),
            Right(c) => c
        }))
    }
}

/// `(a => (b ∨ c))  =>  (a => b) ∨ (a => c)`.
pub fn or_split_dc<A: Prop, B: Prop, C: DProp>(
    f: Imply<A, Or<B, C>>
) -> Or<Imply<A, B>, Imply<A, C>> {
    match C::decide() {
        Left(c) => Right(c.map_any()),
        Right(nc) => Left(Rc::new(move |a| match f(a) {
            Left(b) => b,
            Right(c) => not::absurd(nc.clone(), c)
        }))
    }
}

/// `a  =>  (b => (a ∧ b))`.
pub fn and_map<A: Prop, B: Prop>(a: A) -> Imply<B, And<A, B>> {
    Rc::new(move |b| (a.clone(), b))
}
