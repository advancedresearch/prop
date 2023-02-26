//! # Functional programming as propositions
//!
//! Model is derived from PSQ, PSI and HOOO EP.
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
//! - Identity: `FId` is the identity morphism `id` from any object `A` to `A`
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
//! The identity `id` (`FId`) has itself as an inverse `inv(id) ~~ id`.
//! From this, one can prove `~id`. Using `~id{A} : ~(A -> A)` it is possible to prove `~(A -> A)`.
//!
//! Now, it turns out that the proposition `A -> A`, or `A^A`, for any `A` is tautologically true.
//! Therefore, one can prove `~true` (`true_qu`) and as consequence:
//!
//! - `~true == true` ([eq_qu_true_true])
//! - `~false == false` ([eq_qu_false_false])
//!
//! This is amazing because it is a sophisticated result of Path Semantics using
//! PSI/PSQ/HOOO EP and Category Theory. One might expect that fundamental Path Semantics can
//! provide useful mathematical language design, but it is surprising that useful design can
//! provide insights/theorems into fundamental Path Semantics. The theorems above are not provable
//! using PSI/PSQ/HOOO EP alone.

use crate::*;
use path_semantics::{POrdProof, Ty};
use quality::Q;
use qubit::{Qu, Qubit};
use hooo::{Exists, Para, Pow, Tauto, Theory};
use hooo::pow::PowExt;
use nat::{Nat, S, Z};
use univalence::HomEq3;

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
pub use ty::*;

mod app;
mod comp;
mod dup;
mod id;
mod is_const;
mod lam;
mod norm;
mod subst;
mod tup;
mod ty;

pub mod bool_alg;
pub mod dep;
pub mod eqx;
pub mod feq;
pub mod fin;
pub mod fnat;
pub mod fun_ext;
pub mod inv;
pub mod list;
pub mod phott;
pub mod real;
