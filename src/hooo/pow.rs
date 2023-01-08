//! Power extensions.

use super::*;

/// Extends tautologies with convenient methods.
pub trait PowExt<A: Prop, B: Prop>: Sized {
    /// Transitivity.
    fn trans<C: Prop>(&self, f: Pow<C, B>) -> Pow<C, A>;
}

impl<A: Prop, B: Prop> PowExt<A, B> for Pow<B, A> {
    fn trans<C: Prop>(&self, f: Pow<C, B>) -> Pow<C, A> {pow_transitivity(self.clone(), f)}
}
