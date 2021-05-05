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

/// A proposition that might be decidable or undecidable.
pub trait Prop: 'static + Sized + Clone {
    /// Get double negation rule from proof.
    fn double_neg(self) -> Dneg<Self> {self.map_any()}
    /// Maps anything into itself.
    fn map_any<T>(self) -> Imply<T, Self> {Rc::new(move |_| self.clone())}
}
impl<T: 'static + Sized + Clone> Prop for T {}

/// Implemented by decidable types.
pub trait Decidable: Prop {
    /// Get excluded middle rule.
    fn decide() -> ExcM<Self>;
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
            (_, Left(b)) => Left(b.map_any()),
            (Left(a), Right(b)) =>
                Right(Rc::new(move |f| b.clone()(f(a.clone())))),
            (Right(a), _) => {
                let g: Imply<Not<U>, Not<T>> = a.map_any();
                Left(imply::rev_modus_tollens(g))
            }
        }
    }
}

/// Shorthand for decidable proposition.
pub trait DProp: Decidable {}
impl<T: Decidable> DProp for T {}
