//! # Avatar Extensions
//!
//! Avatar Extensions introduces avatars
//! which are ways to wrap or unwrap propositions.
//!
//! For more information, see
//! https://advancedresearch.github.io/avatar-extensions/summary.html

#![allow(unreachable_code)]

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
#[derive(Clone)]
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
    fn mul(_: T, b: U) -> Self {
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
    fn commute(self) -> Self::Out {and::symmetry(self)}
}

impl<T: Prop, U: Prop> Commutative<T, U> for Eq<T, U> {
    type Out = Eq<U, T>;
    fn commute(self) -> Self::Out {eq::symmetry(self)}
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
#[derive(Clone)]
pub struct Inv<T>(T);

impl<T> Inv<Inv<T>> {
    /// `--a => a`.
    pub fn rev_double(self) -> T {(self.0).0}

    /// `a => --a`.
    pub fn double(a: T) -> Self {Inv(Inv(a))}
}

impl<T: Product<U, V>, U, V> Product<U, V> for Inv<T> {
    fn mul(a: U, b: V) -> Self {
        Inv(T::mul(a, b))
    }
}

impl<T> Avatar<Inv<T>> for Inv<T> {
    type Out = T;
    fn inv(self) -> T {self.0}
}
impl<T> Avatar<Inv<T>> for T {
    type Out = Inv<T>;
    fn inv(self) -> Inv<T> {Inv(self)}
}

/// Implemented by contravariant products.
pub trait Contravariant<T, U>: Product<T, U> {
    /// The contravariant product type.
    type Out: Product<Inv<U>, Inv<T>>;
    /// Gets the contravariant product.
    fn contra(self) -> Self::Out;
}

impl<T: Prop, U: Prop> Contravariant<T, U> for Inv<Imply<T, U>> {
    type Out = Imply<Inv<U>, Inv<T>>;
    fn contra(self) -> Self::Out {
        unimplemented!()
    }
}

impl<T: Prop, U: Prop> Contravariant<Inv<T>, Inv<U>> for Imply<Inv<T>, Inv<U>> {
    type Out = Inv<Imply<Inv<Inv<U>>, Inv<Inv<T>>>>;
    fn contra(self) -> Self::Out {
        unimplemented!()
    }
}

/// An anti-commutative product.
#[derive(Clone)]
pub struct AntiMul<T, U>(T, U);

impl<T, U> AntiMul<Inv<Inv<T>>, Inv<Inv<U>>> {
    /// `(--a * --b)  =>  a * b`.
    pub fn rev_double(self) -> AntiMul<T, U> {
        AntiMul(((self.0).0).0, ((self.1).0).0)
    }
}

impl<T, U> Inv<AntiMul<Inv<Inv<T>>, Inv<Inv<U>>>> {
    /// `-(--a * --b)  =>  -(a * b)`.
    pub fn rev_double(self) -> Inv<AntiMul<T, U>> {
        Inv(self.0.rev_double())
    }
}

impl<T, U> Product<T, U> for AntiMul<T, U> {
    fn mul(a: T, b: U) -> Self {AntiMul(a, b)}
}

impl<T, U> Contravariant<T, U> for Inv<AntiMul<T, U>> {
    type Out = AntiMul<Inv<U>, Inv<T>>;
    fn contra(self) -> Self::Out {
        AntiMul(Inv((self.0).1), Inv((self.0).0))
    }
}
impl<T, U> Contravariant<Inv<T>, Inv<U>> for AntiMul<Inv<T>, Inv<U>> {
    type Out = Inv<AntiMul<Inv<Inv<U>>, Inv<Inv<T>>>>;
    fn contra(self) -> Self::Out {
        Inv(AntiMul(Inv(Inv((self.1).0)), Inv(Inv((self.0).0))))
    }
}
