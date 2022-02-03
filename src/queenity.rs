//! # Seshatic Queenity
//!
//! Seshatic Queenity is a Seshatic relation that "points directly".
//! See [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatic-queenity.pdf).
//!
//! A Seshatic relation means it is strictly directional or looping on itself.
//! For more information, see the documentation for the "quality" module.
//!
//! ### Intuition
//!
//! Seshatic Queenity models a particular relationship
//! where a queen has no queens above her,
//! therefore there are no queens below her.
//! Every subordinate of the queen, is subordinated the queen directly.
//!
//! The queen always queens herself (`a ¬> a`).
//! This means she has the same relation to herself
//! that every subordinate has to her.
//!
//! Seshatic Queenity is more "relaxed" than self-inquality `¬(a ~~ a)` (Seshatism).
//! Under Seshatism, the Self has same relation to itself as to every other proposition.
//! Seshatism is global, while Seshatic Queenity is local.
//! Furthermore, Seshatic Queenity determines the direction toward the Self.
//! Seshatism can be symmetric, but Seshatic Queenity is asymmetric.
//!
//! ### Transitivity
//!
//! Seshatic Queenity is transitive.
//!
//! This can seem confusing, because transitivity intuitively models a middle-queen,
//! which is precisely what Seshatic Queenity forbids.
//!
//! However, without proofs of symbolic distinction,
//! there is no way to explicitly forbit the middle-queen.
//! This means that Seshatic Queenity can be transitive without problems.

use crate::*;

use quality::{EqQ, Q};

/// Prevents other queens of `A` from excluding queen `B`.
pub trait NoOtherSq<A, B>: 'static + Clone {
    /// `(a ¬> c) => ¬¬(a ¬> b)`.
    fn no_other_sq<C: Prop>(&self, sq: Sq<A, C>) -> Not<Not<Sq<A, B>>>;
}

/// If `A`'s queen is `C`, then `C` is equal to `B`.
pub trait UniqSq<A, B>: NoOtherSq<A, B> {
    /// `(a ¬> c) => (c == b)`.
    fn uniq_sq<C: Prop>(&self, sq: Sq<A, C>) -> Eq<C, B>;
}

/// Queenity between `A` and `B` (`A ¬> B`).
#[derive(Clone)]
pub struct Sq<A, B>(pub(crate) Imply<A, B>);

/// Converts queenity to implication `(a ¬> b) => (a => b)`.
pub fn to_imply<A: Prop, B: Prop>(Sq(f): Sq<A, B>) -> Imply<A, B> {f}

/// `(a ¬> b) ⋀ ((a == b) => (a ~~ b))  =>  ¬(a ¬> a)`
///
/// Gets self-queenity of the left side when `a` and `b` are symbolic distinct.
pub fn nsq_left<A: Prop, B: Prop>(
    _sq: Sq<A, B>,
    _eq_q: EqQ<A, B>
) -> Not<Sq<A, A>> {unimplemented!()}

/// Gets self-queenity of right side `(a ¬> b) => (b ¬> b)`.
pub fn sq_right<A: Prop, B: Prop>(_sq: Sq<A, B>) -> Sq<B, B> {
    Sq(Rc::new(move |b| b))
}

/// Converts queenity to inquality `(a ¬> b) => ¬(a ~~ b)`.
pub fn to_sesh<A: Prop, B: Prop>(_sq: Sq<A, B>) -> Not<Q<A, B>> {
    unimplemented!()
}

/// `(a ¬> b) ⋀ (b ¬> c) => (a ¬> c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    Sq(ab): Sq<A, B>,
    Sq(bc): Sq<B, C>,
) -> Sq<A, C> {
    Sq(Rc::new(move |a| bc(ab(a))))
}

/// `(a ¬> b) ∧ (a = c)  =>  (c ¬> b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(Sq(f): Sq<A, B>, (_, g1): Eq<A, C>) -> Sq<C, B> {
    Sq(imply::transitivity(g1, f))
}

/// `(a ¬> b) ∧ (b = c)  =>  (a ¬> c)`.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(Sq(f): Sq<A, B>, (g0, _): Eq<B, C>) -> Sq<A, C> {
    Sq(imply::transitivity(f, g0))
}
