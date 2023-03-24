//! Tactics for Logical OR.

#![allow(unreachable_code)]

use crate::*;

/// `a ∨ b => b ∨ a`.
pub fn symmetry<A: Prop, B: Prop>(or: Or<A, B>) -> Or<B, A> {
    use Either::*;

    match or {
        Left(x) => Right(x),
        Right(x) => Left(x)
    }
}

/// `(a ∨ b) ∨ c  =>  a ∨ (b ∨ c)`
pub fn assoc<A: Prop, B: Prop, C: Prop>(
    f: Or<Or<A, B>, C>
) -> Or<A, Or<B, C>> {
    use Either::*;

    match f {
        Left(x) => match x {
            Left(a) => Left(a),
            Right(b) => Right(Left(b)),
        }
        Right(c) => Right(Right(c))
    }
}

/// `(a ∧ b) ∨ (a ∧ c)  =>  a ∧ (b ∨ c)`
pub fn distrib<A: Prop, B: Prop, C: Prop>(
    x: Or<And<A, B>, And<A, C>>
) -> And<A, Or<B, C>> {
    use Either::*;

    match x {
        Left((a, b)) => (a, Left(b)),
        Right((a, c)) => (a, Right(c))
    }
}

/// `¬(a ∧ b) => (¬a ∨ ¬b)`.
pub fn from_de_morgan<A: DProp, B: DProp>(
    f: Not<And<A, B>>
) -> Or<Not<A>, Not<B>> {
    use Either::*;

    match (A::decide(), B::decide()) {
        (Left(a), Left(b)) => match f((a, b)) {},
        (_, Right(b)) => Right(Rc::new(move |x| b.clone()(x))),
        (Right(a), _) => Left(Rc::new(move |x| a.clone()(x))),
    }
}

/// `(¬a ∨ ¬b) => ¬(a ∧ b)`.
pub fn to_de_morgan<A: Prop, B: Prop>(f: Or<Not<A>, Not<B>>) -> Not<And<A, B>> {
    Rc::new(move |(a, b)| match f.clone() {
        Left(fa) => fa(a),
        Right(fb) => fb(b)
    })
}

/// `(a ∨ b) ∧ (a => c)  =>  (c ∨ b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(
    or_x_y: Or<A, B>, g: Imply<A, C>
) -> Or<C, B> {
    match or_x_y {
        Left(x) => Left(g(x)),
        Right(y) => Right(y),
    }
}

/// `(a ∨ b) ∧ (b => c)  =>  (a ∨ c)`.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(
    or_x_y: Or<A, B>, g: Imply<B, C>
) -> Or<A, C> {
    match or_x_y {
        Left(x) => Left(x),
        Right(y) => Right(g(y)),
    }
}

/// `(¬a ∧ b) ∨ a  =>  (b ∨ a)`.
pub fn bound_neg<A: Prop, B: Prop>(f: Or<And<Not<A>, B>, A>) -> Or<B, A> {
    match f {
        Left((_, b)) => Left(b),
        Right(a) => Right(a)
    }
}

/// `(a ∧ b) ∨ ¬a  =>  (b ∨ ¬a)`.
pub fn bound_pos<A: Prop, B: Prop>(f: Or<And<A, B>, Not<A>>) -> Or<B, Not<A>> {
    match f {
        Left((_, b)) => Left(b),
        Right(not_a) => Right(not_a)
    }
}

/// `¬¬a == (a ∨ ¬¬a)`.
pub fn eq_nn<A: Prop, B: Prop>() -> Eq<Not<Not<A>>, Or<A, Not<Not<A>>>> {
    (
        Rc::new(move |x| Right(x)),
        Rc::new(|x| match x {
            Left(a) => not::double(a),
            Right(nna) => nna,
        }),
    )
}

/// `a ∨ a  =>  a`.
pub fn both<A: Prop>(x: Or<A, A>) -> A {
    match x {
        Left(a) => a,
        Right(a) => a,
    }
}
