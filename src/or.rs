//! Tactics for Logical OR.

use crate::*;

/// `a ∨ b => b ∨ a`.
pub fn commute<A: Prop, B: Prop>(or: Or<A, B>) -> Or<B, A> {
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
pub fn from_de_morgan<A: Prop, B: Prop>(
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
pub fn to_de_morgan<A: Prop, B: Prop>(
    f: Or<Not<A>, Not<B>>
) -> Not<And<A, B>> {
    use Either::*;

    match f {
        Left(fa) => match A::decide() {
            Left(a) => match fa(a) {},
            Right(not_a) => Rc::new(move |(x, _)| match not_a.clone()(x) {}),
        }
        Right(fb) => match B::decide() {
            Left(b) => match fb(b) {},
            Right(not_b) => Rc::new(move |(_, x)| match not_b.clone()(x) {}),
        }
    }
}
