//! # Functional programming as propositions
//!
//! Model is derived from PSQ, PSI and HOOO EP.
//!
//! ### Introduction to Functional Programming
//!
//! In computer science, functional programming is a programming paradigm where programs are
//! constructed by applying and composing functions. For more information,
//! see [wikipedia article](https://en.wikipedia.org/wiki/Functional_programming).
//!
//! Foundational Path Semantics (PSI/PSQ/HOOO EP) is lower level than functional programming.
//!
//! For example, `a : T` in functional programming is a primitive notion, which can not be reduced
//! to something else. However, in foundational Path Semantics, `a : T` might be modelled as
//! `(a => T) ⋀ (a < T)` where `<` is path semantical order.
//!
//! Notice that in Rust, `a : T` is built into the language itself.
//! The problem is that Rust does not support e.g. dependent types.
//! This is why foundational Path Semantics is needed,
//! to prove properties of higher level languages with more complex type systems than Rust.
//! The motivation is to use a small set of axioms, powerful enough to develop some intuition
//! in isolation, but also can be used as a starting point for more advanced logical frameworks.
//!
//! There are many theorems that are provable in foundational Path Semantics,
//! which are not provable in normal functional programming. Therefore, one should think about
//! foundational Path Semantics as a more general model of mathematics.
//!
//! Normal functional programming can be thought of as a "library" written in foundational
//! Path Semantics. New operators and definitions are made using new axioms.
//! However, these new axioms work in harmony with existing axioms.
//!
//! For example, function composition `g . f` is not a primitive notion that is built into
//! foundational Path Semantics. This operator needs to be defined and axioms introduced that
//! describe mathematical properties of function composition. When these new axioms are defined,
//! one can use them to prove theorems about function composition.
//!
//! ### Types
//!
//! A type `x : T` uses `Ty<X, T>` from the [path_semantics] module (PSI).
//!
//! A function type `f : X -> Y` uses `Ty<F, Pow<Y, X>>` from the [hooo] module (HOOO EP).
//!
//! A lambda/closure type `f : X => Y` uses `Ty<F, Imply<X, Y>>`.
//!
//! ### Imaginary Inverse
//!
//! For information about the imaginary inverse, see the [fun::inv] module.
//!
//! ### Function Extensionality
//!
//! For information about function extensionality, see the [fun::fun_ext] module.
//!
//! ### Dependent Types
//!
//! For information about dependent types, see the [fun::dep] module.
//!
//! ### Category Theory Perspective
//!
//! This model seen from a Category Theory perspective produces an ∞-groupoid.
//!
//! - Object: `A: Prop` as generic argument is an object `A` in the ∞-groupoid
//! - Morphism: `Ty<F, Pow<B, A>>` is a morphism `F` from `A` to `B`, `f : A -> B`
//! - Identity: `Id<A>` is the identity morphism `id{A} : A -> A`
//! - Composition: `Comp<G, F>` is the composition `g . f`
//! - Inverse: `Inv<F>` is the imaginary inverse `inv(f)`
//!
//! The imaginary inverse adds an inverse for every morphism in the category,
//! which results in a groupoid. However, since the inverse is imaginary,
//! [the groupoid is category realizable](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/category-realizable-groupoids.pdf).
//!
//! Any expression constructed from these operations can be used where `A: Prop` is allowed.
//! Therefore, morphisms and higher morphisms are also objects, hence this form an ∞-groupoid.
//!
//! ### Qubit Truths
//!
//! For information about qubit truths, see the [fun::id] module.

use crate::*;
use path_semantics::{ty, POrdProof, Ty};
use quality::Q;
use qubit::Qu;
use hooo::{Exists, Para, Pow, Tauto, Theory};
use hooo::pow::PowExt;
use nat::{Nat, S, Z};

pub use app::*;
pub use comp::*;
pub use dep::*;
pub use dup::*;
pub use feq::*;
pub use id::*;
pub use inv::*;
pub use is_const::*;
pub use lam::*;
pub use norm::*;
pub use subst::*;
pub use tup::*;
pub use typ::*;

mod app;
mod comp;
mod dup;
mod is_const;
mod lam;
mod norm;
mod subst;
mod tup;
mod typ;

pub mod bool_alg;
pub mod dep;
pub mod eqx;
pub mod feq;
pub mod fin;
pub mod fnat;
pub mod fun_ext;
pub mod id;
pub mod inv;
pub mod list;
pub mod phott;
pub mod real;
