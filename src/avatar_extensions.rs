//! # Avatar Extensions
//!
//! Avatar Extensions introduces avatars
//! which are ways to wrap or unwrap propositions.
//!
//! For more information, see
//! https://advancedresearch.github.io/avatar-extensions/summary.html

use crate::*;

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

/// Implemented by avatars that have their "clothes on".
pub trait Uniform: Sized + Avatar<Self> {}

impl<T: Avatar<T>> Uniform for T {}

/// Implemented by avatars that have their "clothes off".
pub trait NonUniform<T>: Sized + Avatar<T, Out = T> {}

impl<U, T: Avatar<U, Out = U>> NonUniform<U> for T {}

/// Loop Witness.
pub trait LoopWitness: Sized + Uniform + NonUniform<Self> {}

impl<T: Avatar<T, Out = T>> LoopWitness for T {}

/// Loop.
pub struct Loop<T>(pub T);

impl<T> Avatar<Loop<T>> for Loop<T> {
    type Out = Loop<T>;
    fn inv(self) -> Self::Out {self}
}

/// Gets a loop witness from product witness.
pub fn to_loop<T: Uniform>(p: T) -> Loop<T::Out> {
    Loop(p.inv())
}
