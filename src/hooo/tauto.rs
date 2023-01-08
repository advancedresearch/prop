//! Tautology extensions.

use super::*;

/// Extends tautologies with convenient methods.
pub trait TautoExt<A: Prop>: Sized {
    /// Apply map lifted to tautology.
    fn tapp<B: Prop>(&self, f: Pow<B, A>) -> Tauto<B>;
}

impl<A: Prop> TautoExt<A> for Tauto<A> {
    fn tapp<B: Prop>(&self, f: Pow<B, A>) -> Tauto<B> {
        hooo_imply(pow_to_imply_lift(f))(self.clone())
    }
}

/// Maps expression to tautology.
#[macro_export]
macro_rules! tauto(($x:expr) => {|_: True| $x});
