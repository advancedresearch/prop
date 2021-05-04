//! Tactics for Logical AND.

use crate::*;

/// `a ∧ b => b ∧ a`.
fn commute<A: Prop, B: Prop>((f0, f1): And<A, B>) -> And<B, A> {
    (f1, f0)
}
