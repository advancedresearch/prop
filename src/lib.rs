#![deny(missing_docs)]

//! # Prop
//! Propositional logic with types in Rust.

use std::rc::Rc;

pub mod imply;
pub mod eq;

/// Logical true.
#[derive(Copy, Clone)]
pub struct True;
/// Logical false.
#[derive(Copy, Clone)]
pub enum False {}

/// Sum type of left and right case.
pub enum Either<T, U> {
    /// Left case.
    Left(T),
    /// Right case.
    Right(U),
}

/// Logical AND.
pub type And<T, U> = (T, U);
/// Double negation.
pub type Dneg<T> = Imply<Not<Not<T>>, T>;
/// Logical EQ.
pub type Eq<T, U> = And<Imply<T, U>, Imply<U, T>>;
/// Logical IMPLY.
pub type Imply<T, U> = Rc<dyn Fn(T) -> U>;
/// Excluded middle.
pub type ExcM<T> = Or<T, Not<T>>;
/// Logical NOT.
pub type Not<T> = Imply<T, False>;
/// Logical OR.
pub type Or<T, U> = Either<T, U>;

/// Implemented by decidable types.
pub trait Decidable: 'static + Sized + Copy {
    /// Get excluded middle rule.
    fn decide() -> ExcM<Self>;
    /// Get double negation rule from instance.
    fn double_neg(self) -> Dneg<Self> {
        Rc::new(move |_| match Self::decide() {
            Either::Left(a) => a,
            Either::Right(not_a) => match not_a(self) {},
        })
    }
}
impl Decidable for True {
    fn decide() -> ExcM<True> {Either::Left(True)}
}
impl Decidable for False {
    fn decide() -> ExcM<False> {Either::Right(Rc::new(move |x| x))}
}

/// Shorthand for proposition.
///
/// Implemented by `True` and `False`.
pub trait Prop: Decidable {}
impl Prop for True {}
impl Prop for False {}
