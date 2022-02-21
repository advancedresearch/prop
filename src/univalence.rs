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
use nat::{Dec, Lt, Nat, Z};
use path_semantics::Ty;

/// A homotopy path between paths `A` and `B`.
pub type Hom<A, B> = Imply<Imply<A, B>, Q<A, B>>;

/// Quality univalence: Equality is qual to quality.
pub type Univ<A, B> = Q<Eq<A, B>, Q<A, B>>;

/// Univalence from equality.
pub type EqUniv<A, B> = Imply<Eq<A, B>, Univ<A, B>>;

/// `((a == b) => ((a == b) ~~ (a ~~ b))) => ((a == b) => (a ~~ b))`.
pub fn eq_univ_to_eqq<A: Prop, B: Prop>(p: EqUniv<A, B>) -> EqQ<A, B> {
    Rc::new(move |eq| quality::to_eq(p(eq.clone())).0(eq))
}

/// `((a == b) => (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn eqq_to_univ<A: Prop, B: Prop>(p: EqQ<A, B>) -> Univ<A, B> {
    eq_lift((
        Rc::new(move |eq| p(eq)),
        Rc::new(move |q| quality::to_eq(q))
    ))
}

/// `((a == b) ~~ (a ~~ b)) => ((a == b) => (a ~~ b))`.
pub fn univ_to_eqq<A: Prop, B: Prop>(univ: Univ<A, B>) -> EqQ<A, B> {
    eq_univ_to_eqq(univ.map_any())
}

/// Lift `(a == b) == (a ~~ b)` to `(a == b) ~~ (a ~~ b)`.
pub fn eq_lift<A: Prop, B: Prop>(eq_eq_q: Eq<Eq<A, B>, Q<A, B>>) -> Univ<A, B> {
    Q(eq_eq_q)
}

/// `((a => b) => (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn hom_to_univ<A: Prop, B: Prop>(hom: Hom<A, B>) -> Univ<A, B> {
    eq_lift((
        Rc::new(move |eq| hom(eq.0)),
        Rc::new(move |q| quality::to_eq(q)),
    ))
}

/// `((a == b) => (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn hom_eq_q<A: Prop, B: Prop>() -> Hom<Eq<A, B>, Q<A, B>> {
    Rc::new(move |x| eqq_to_univ(x))
}

/// `((a == b) == (a ~~ b)) ~~ ((a == b) ~~ (a ~~ b))`.
pub fn univ_eq_q<A: Prop, B: Prop>() -> Univ<Eq<A, B>, Q<A, B>> {
    hom_to_univ(hom_eq_q())
}

/// `((a == b) == (a ~~ b)) => ((a == b) ~~ (a ~~ b))`.
pub fn eqq_eq_q<A: Prop, B: Prop>() -> EqQ<Eq<A, B>, Q<A, B>> {
    univ_to_eqq(univ_eq_q())
}

/// Higher quality univalence.
pub fn higher<A: Prop, B: Prop>(univ: Univ<A, B>) -> Univ<Eq<A, B>, Q<A, B>> {
    let eq: Eq<Eq<A, B>, Q<A, B>> = quality::to_eq(univ.clone());
    let higher_eq: Eq<_, Univ<A, B>> = (univ.map_any(), eq.map_any());
    eq_lift::<Eq<A, B>, Q<A, B>>(higher_eq)
}

/// Homotopy level.
///
/// For theoretical background, see [nLab - homotopy levels](https://ncatlab.org/nlab/show/homotopy+level).
pub trait HomotopyLevel<N: Nat>: Prop {
    /// Returns a quality for the homotopy level below.
    ///
    /// Uses symbolic distinction to model inhabitation of a type.
    /// This is only required at homotopy level 0.
    /// When `x == y`, one can prove `x ~~ y` only if they are symbolic distinct.
    /// Relative to the core axiom of path semantics,
    /// this implies that their types are qual.
    /// Since this produces a self-quality on the homotopy level,
    /// it is interpreted as the type being inhabited.
    fn h_level<X: Prop, Y: Prop>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>,
        eqq_xy: Imply<Eq<N, Z>, EqQ<X, Y>>,
    ) -> Q<X, Y>
        where Q<X, Y>: HomotopyLevel<<N as Dec>::Out>;

    /// Homotopy level 0.
    fn h0<X: Prop, Y: Prop>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>,
        eqq_xy: EqQ<X, Y>,
    ) -> Q<X, Y>
        where Q<X, Y>: HomotopyLevel<Z>,
              Self: HomotopyLevel<Z>
    {
        <Self as HomotopyLevel<Z>>::h_level(ty_x, ty_y, eqq_xy.map_any())
    }

    /// Homotopy level `N` where `N > 0`.
    fn hn<X: Prop, Y: Prop>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>,
    ) -> Q<X, Y>
        where Q<X, Y>: HomotopyLevel<<N as Dec>::Out>,
              Z: Lt<N>
    {
        let neq_nz: Not<Eq<N, Z>> = eq::neq_symmetry(nat::lt_neq());
        Self::h_level(ty_x, ty_y,
            Rc::new(move |eq_nz| not::absurd(neq_nz.clone(), eq_nz)))
    }
}
