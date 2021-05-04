#![deny(missing_docs)]
#![deny(dead_code)]

//! # Prop
//! Propositional logic with types in Rust.

use std::rc::Rc;

use Either::*;

pub mod and;
pub mod imply;
pub mod eq;
pub mod not;
pub mod or;

/// Logical true.
#[derive(Copy, Clone)]
pub struct True;
/// Logical false.
#[derive(Copy, Clone)]
pub enum False {}

/// Sum type of left and right case.
#[derive(Copy, Clone)]
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
pub trait Decidable: 'static + Sized + Clone {
    /// Get excluded middle rule.
    fn decide() -> ExcM<Self>;
    /// Get double negation rule from instance.
    fn double_neg(self) -> Dneg<Self> {self.map_any()}
    /// Maps any time into itself.
    fn map_any<T>(self) -> Imply<T, Self> {Rc::new(move |_| self.clone())}
}

impl Decidable for True {
    fn decide() -> ExcM<True> {Left(True)}
}
impl Decidable for False {
    fn decide() -> ExcM<False> {Right(Rc::new(move |x| x))}
}
impl<T, U> Decidable for And<T, U> where T: Decidable, U: Decidable {
    fn decide() -> ExcM<Self> {
        match (<T as Decidable>::decide(), <U as Decidable>::decide()) {
            (Left(a), Left(b)) => Left((a, b)),
            (_, Right(b)) => Right(Rc::new(move |(_, x)| b.clone()(x))),
            (Right(a), _) => Right(Rc::new(move |(x, _)| a.clone()(x))),
        }
    }
}
impl<T, U> Decidable for Or<T, U> where T: Decidable, U: Decidable {
    fn decide() -> ExcM<Self> {
        match (<T as Decidable>::decide(), <U as Decidable>::decide()) {
            (Left(a), _) => Left(Left(a)),
            (_, Left(b)) => Left(Right(b)),
            (Right(a), Right(b)) => Right(Rc::new(move |f| match f {
                Left(x) => a.clone()(x),
                Right(y) => b.clone()(y),
            }))
        }
    }
}
impl<T, U> Decidable for Imply<T, U> where T: Decidable, U: Decidable {
    fn decide() -> ExcM<Self> {
        match (<T as Decidable>::decide(), <U as Decidable>::decide()) {
            (_, Left(b)) => Left(Rc::new(move |_| b.clone())),
            (Left(a), Right(b)) => Right(Rc::new(move |f| b.clone()(f(a.clone())))),
            (Right(a), Right(b)) => {
                let g: Imply<Not<U>, Not<T>> = Rc::new(move |_| a.clone());
                Left(imply::rev_modus_tollens(g))
            }
        }
    }
}

/// Shorthand for proposition.
pub trait Prop: Decidable {}
impl<T: Decidable> Prop for T {}
