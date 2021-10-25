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

/// Implemented by products.
pub trait Product<T, U> {
    /// Creates a product out of two propositions.
    fn mul(a: T, b: U) -> Self;
}

impl<T, U> Product<T, U> for And<T, U> {
    fn mul(a: T, b: U) -> Self {(a, b)}
}

impl<T: Prop, U: Prop> Product<T, U> for Eq<T, U> {
    fn mul(a: T, b: U) -> Self {
        (Rc::new(move |_| b.clone()),
         Rc::new(move |_| a.clone()))
    }
}

impl<T, U: Prop> Product<T, U> for Imply<T, U> {
    fn mul(a: T, b: U) -> Self {
        Rc::new(move |_| b.clone())
    }
}

/// Implememnted by commutative products.
pub trait Commutative<T, U>: Product<T, U> {
    /// The output type for commuted product.
    type Out: Commutative<U, T>;
    /// Commutes product.
    fn commute(self) -> Self::Out;
}

impl<T: Prop, U: Prop> Commutative<T, U> for And<T, U> {
    type Out = And<U, T>;
    fn commute(self) -> Self::Out {and::commute(self)}
}

impl<T: Prop, U: Prop> Commutative<T, U> for Eq<T, U> {
    type Out = Eq<U, T>;
    fn commute(self) -> Self::Out {eq::commute(self)}
}

/// `a ∧ b  =>  -(a * b) = (-a) * b`.
pub fn left_cover_by_proof<
    A: Prop + NonUniform<Pa>,
    B: Prop,
    M1: Product<A, B> + NonUniform<PM1>,
    M2: Product<Pa, B>,
    Pa,
    PM1,
>(a: A, b: B) -> Eq<PM1, M2> {
    let a2 = a.clone();
    let b2 = b.clone();
    (
        Rc::new(move |_| M2::mul(a2.clone().inv(), b2.clone())),
        Rc::new(move |_| M1::mul(a.clone(), b.clone()).inv())
    )
}

/// `a ∧ b  =>  -(a * b) = a * (-b)`.
pub fn right_cover_by_proof<
    A: Prop,
    B: Prop + NonUniform<Pb>,
    M1: Product<A, B> + NonUniform<PM1>,
    M2: Product<A, Pb>,
    Pb,
    PM1,
>(a: A, b: B) -> Eq<PM1, M2> {
    let a2 = a.clone();
    let b2 = b.clone();
    (
        Rc::new(move |_| M2::mul(a2.clone(), b2.clone().inv())),
        Rc::new(move |_| M1::mul(a.clone(), b.clone()).inv())
    )
}

/// Imaginary inverse.
///
/// This is prevented from leaking
/// by not having access to the inner object.
pub struct Inv<T>(T);

impl<T> Avatar<Inv<T>> for Inv<T> {
    type Out = T;
    fn inv(self) -> T {self.0}
}
impl<T> Avatar<Inv<T>> for T {
    type Out = Inv<T>;
    fn inv(self) -> Inv<T> {Inv(self)}
}

impl<T, U: Prop> Product<T, U> for Inv<Imply<T, U>> {
    fn mul(a: T, b: U) -> Self {
        Inv(Rc::new(move |_| b.clone()))
    }
}

impl<T, U: Prop> Product<T, U> for Imply<Inv<T>, Inv<U>> {
    fn mul(a: T, b: U) -> Self {
        Rc::new(move |_| Inv(b.clone()))
    }
}

