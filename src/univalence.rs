//! # Quality Univalence
//!
//! Helper methods for reasoning about Quality Univalence.
//! For more information about Quality, see the documentation of the "quality" module.
//!
//! Equality `==` has the property that left or right side can be substituted.
//! Univalence is the idea that a different form of equivalence (partial or total),
//! can be converted back and forth with equality and this translation back and forth itself
//! is also an equivalence.
//!
//! From `(a == b) => (a ~~ b)`, one can prove `(a == b) == (a ~~ b)`.
//! However, this is not strong enough to prove `(a == b) ~~ (a ~~ b)`.
//! The latter is called "Quality Univalence".
//!
//! ### Quality vs Homotopy Univalence
//!
//! Quality Univalence differs from Homotopy Univalence by these properties:
//!
//! - Quality: `(a == b) => (a ~~ b)` (Equality implies Quality)
//! - Homotopy: `(a => b) => (a ~= b)` (Implication implies Equivalence)
//!
//! The Homotopy Univalence axiom is the following:
//!
//! `(a == b) ~= (a ~= b)`
//!
//! Under the homotopy univalence axiom with path semantical quality,
//! quality univalence is equal to homotopy univalence.
//! Since equality is homotopic equivalent to homotopy equivalence,
//! and equality is qual to quality, it means `~=` can be replaced by `~~`.

use crate::*;
use quality::*;

/// A homotopy path between paths `A` and `B`.
pub type Hom<A, B> = Imply<Imply<A, B>, Q<A, B>>;

/// Quality univalence: Equality is qual to quality.
pub type Univ<A, B> = Q<Eq<A, B>, Q<A, B>>;

/// Univalence from equality.
pub type EqUniv<A, B> = Imply<Eq<A, B>, Univ<A, B>>;

/// `((a == b) => ((a == b) ~~ (a ~~ b))) => ((a == b) => (a ~~ b))`.
pub fn eq_univ_to_eq_q<A: Prop, B: Prop>(p: EqUniv<A, B>) -> EqQ<A, B> {
    Rc::new(move |eq| quality::to_eq(p(eq.clone())).0(eq))
}

/// `((a == b) => (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn eq_q_to_univ<A: Prop, B: Prop>(p: EqQ<A, B>) -> Univ<A, B> {
    eq_lift((
        Rc::new(move |eq| p(eq)),
        Rc::new(move |q| quality::to_eq(q))
    ))
}

/// `((a == b) ~~ (a ~~ b)) => ((a == b) => (a ~~ b))`.
pub fn univ_to_eq_q<A: Prop, B: Prop>(univ: Univ<A, B>) -> EqQ<A, B> {
    eq_univ_to_eq_q(univ.map_any())
}

/// `((a => b) => (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn hom_to_univ<A: Prop, B: Prop>(hom: Hom<A, B>) -> Univ<A, B> {
    eq_lift((
        Rc::new(move |eq| hom(eq.0)),
        Rc::new(move |q| quality::to_eq(q)),
    ))
}

/// Lift `(a == b) == (a ~~ b)` to `(a == b) ~~ (a ~~ b)`.
pub fn eq_lift<A: Prop, B: Prop>(eq_eq_q: Eq<Eq<A, B>, Q<A, B>>) -> Univ<A, B> {
    Q(eq_eq_q)
}

/// Higher quality univalence.
pub fn higher<A: Prop, B: Prop>(univ: Univ<A, B>) -> Univ<Eq<A, B>, Q<A, B>> {
    let eq: Eq<Eq<A, B>, Q<A, B>> = quality::to_eq(univ.clone());
    let higher_eq: Eq<_, Univ<A, B>> = (univ.map_any(), eq.map_any());
    eq_lift::<Eq<A, B>, Q<A, B>>(higher_eq)
}

/// `(a ~~ b) ∧ (a == c)  =>  (c ~~ b)`
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(f: Q<A, B>, g: Eq<A, C>) -> Q<C, B> {
    Q(eq::commute(eq::transitivity(eq::commute(quality::to_eq(f)), g)))
}

/// `(a ~~ b) ∧ (b == c)  =>  (a ~~ c)`
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(f: Q<A, B>, g: Eq<B, C>) -> Q<A, C> {
    Q(eq::transitivity(quality::to_eq(f), g))
}
