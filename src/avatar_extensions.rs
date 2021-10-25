//! # Avatar Extensions
//!
//! Avatar Extensions introduces avatars
//! which are ways to wrap or unwrap propositions.
//!
//! For more information, see
//! https://advancedresearch.github.io/avatar-extensions/summary.html

/// Implemented by avatars.
///
/// An avatar is an involution,
/// which means that it maps back to itself
/// after 2 steps.
pub trait Avatar<T> {
    /// The output avatar.
    type Out: Avatar<T, Out = Self>;
    /// Involve the avatar.
    fn inv(self) -> Self::Out;
}

/// Implemented avatars that have their "clothes on".
pub trait Uniform: Sized + Avatar<Self> {}

impl<T: Avatar<T>> Uniform for T {}

/// Loop Witness.
pub trait LoopWitness<P>: Sized + Avatar<Self, Out = Self>
    where P: Avatar<P, Out = Self::Inner>
{
    /// The inner type of the loop witness.
    ///
    /// This is implemented as `P::Out`.
    ///
    /// Since `P` is uniform, the next involution is non-uniform,
    /// which is the inner most possible type.
    type Inner;
}

impl<P, T: Avatar<T, Out = T>> LoopWitness<P> for T
    where P: Uniform
{
    type Inner = P::Out;
}

/// Loop.
pub struct Loop<T>(pub T);

impl<T> Avatar<Loop<T>> for Loop<T> {
    type Out = Loop<T>;
    fn inv(self) -> Self::Out {self}
}

/// Gets a loop from product.
pub fn loop_from_product<T: Uniform>(p: T) -> Loop<T::Out> {
    Loop(p.inv())
}
