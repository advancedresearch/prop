#![deny(missing_docs)]
#![deny(dead_code)]
#![feature(marker_trait_attr)]

//! # Prop
//! Propositional logic with types in Rust.
//!
//! A library in Rust for theorem proving with [Intuitionistic Propositional Logic](https://en.wikipedia.org/wiki/Intuitionistic_logic).
//! Supports theorem proving in [Classical Propositional Logic](https://en.wikipedia.org/wiki/Propositional_calculus).
//!
//! - Used in research on [Path Semantics](https://github.com/advancedresearch/path_semantics)
//! - Brought to you by the [AdvancedResearch Community](https://advancedresearch.github.io/)
//! - [Join us on Discord!](https://discord.gg/JkrhJJRBR2)
//!
//! ### Motivation
//!
//! [Path Semantics](https://github.com/advancedresearch/path_semantics)
//! extends dependent types with normal paths and is also used to extend
//! Classical Propositional Logic with multiple levels of propositions.
//! It is also used to explore higher dimensional mathematics.
//! A popular research subject in Path Semantics is [Avatar Extensions](https://advancedresearch.github.io/avatar-extensions/summary.html).
//!
//! When researching, in some cases it is useful to figure out whether a proof is
//! provable in classical logic, but not in constructive logic.
//! This requires comparing proofs easily.
//!
//! This library uses a lifting mechanism for making it easier
//! to produce proofs in classical logic and compare them to
//! proofs in constructive logic.
//!
//! ### Design
//!
//! This library contains:
//!
//! - `Prop`: Propositions that might or might not be decidable (constructive logic)
//! - `DProp`: Decidable propositions (classical logic)
//! - Automatic lifting of Excluded Middle to decidable propositions
//! - Double Negation for proofs of `Prop`
//! - Formalization of the core axiom of Path Semantics
//! - Tactics organized in modules by constructs (e.g. `and` or `imply`)
//!
//! Due to first-order logic requiring dependent types,
//! which is not yet supported in Rust,
//! this library is limited to zeroth-order logic (propositional logic).
//!
//! ### Examples
//!
//! ```rust
//! use prop::*;
//!
//! fn proof<A: Prop, B: Prop>(f: Imply<A, B>, a: A) -> B {
//!     imply::modus_ponens(f, a)
//! }
//! ```
//!
//! Notice that there is no `DProp` used here,
//! which means that it is a constructive proof.
//!
//! ```rust
//! use prop::*;
//!
//! fn proof<A: DProp, B: DProp>(f: Imply<Not<A>, Not<B>>) -> Imply<B, A> {
//!    imply::rev_modus_tollens(f)
//! }
//! ```
//!
//! Here, `DProp` is needed because `rev_modus_tollens` needs Excluded Middle.
//! This limits the proof to decidable propositions.
//!
//! ### Path Semantics
//!
//! Path Semantics is an extremely expressive language for mathematical programming.
//! It uses a single core axiom, which models semantics of symbols.
//!
//! Basically, mathematical languages contain a hidden symmetry due to use of symbols.
//! Counter-intuitively, symbols are not "inherently" in logic.
//!
//! One way to put it, is that the symbols "themselves" encode laws of mathematics.
//! The hidden symmetry can be exploited to prove semantics and sometimes
//! improve performance of automated theorem provers.
//!
//! For example, path Semantics can be used to boost performance of brute force theorem proving
//! in Classical Propositional Logic on Type-hierarchy-like problems.
//! For more information, see the blog post [Improving Brute Force Theorem Proving](https://advancedresearch.github.io/blog/2020-08-20-improving-brute-force-theorem-proving).
//!
//! For more information, see the [Path Semantics Project](https://github.com/advancedresearch/path_semantics).

use std::rc::Rc;

use Either::*;

pub mod and;
pub mod imply;
pub mod eq;
pub mod not;
pub mod or;
pub mod path_semantics;

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
/// Alternative to Logical EQ.
pub type Iff<T, U> = Eq<T, U>;
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
