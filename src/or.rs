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
