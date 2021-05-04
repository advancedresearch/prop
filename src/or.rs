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
