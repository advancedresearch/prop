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
use nat::{EqNat, Dec, Lt, Nat, S, Z};
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
    /// A type such that proves homotopy level 0.
    type H0: Prop;
    /// A type such that it proves lower homotopy level.
    type H: HomotopyLevel<<N as Dec>::Out>;
    /// Homotopy level 0.
    fn h0<Y: Prop>(ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat;
    /// Higher homotopy level.
    fn hn<X: Prop, Y: Prop>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>;
}

/// Shorthand for homotopy proposition.
pub trait HProp<N: Nat>: HomotopyLevel<N> {}
impl<N: Nat, T: HomotopyLevel<N>> HProp<N> for T {}

/// Lower homotopy level with 2.
pub type H2<A, N> = <<A as HomotopyLevel<S<S<N>>>>::H as HomotopyLevel<S<N>>>::H;

/// Proves that homotopy level 0 has quality between any members.
pub fn hlev0_q<X: Prop, Y: Prop, A: HProp<Z>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
) -> Q<X, Y> {
    let q_zx = A::h0(ty_x);
    let q_zy = A::h0(ty_y);
    let q_xz = quality::symmetry(q_zx);
    quality::transitivity(q_xz, q_zy)
}

/// Proves that homotopy level 1 or higher has quality between self-quality of any members.
pub fn hlev1_q2<X: Prop, Y: Prop, N: Nat, A: HProp<S<N>>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
) -> Q<Q<X, X>, Q<Y, Y>> {
    let q_z_q_xx = A::hn(ty_x.clone(), ty_x);
    let q_z_q_yy = A::hn(ty_y.clone(), ty_y);
    let q_xx_q_z = quality::symmetry(q_z_q_xx);
    let q_xx_q_yy = quality::transitivity(q_xx_q_z, q_z_q_yy);
    q_xx_q_yy
}

/// Lift type of path.
pub fn lift_ty<X: Prop, Y: Prop, X2: Prop, N: Nat, A: HProp<S<N>>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
    ty_x2_q_xy: Ty<X2, Q<X, Y>>,
) -> Ty<X2, A::H> {
    let q_az_q_xy = A::hn(ty_x, ty_y);
    let (x2_q_xy, pord_x2_q_xy) = ty_x2_q_xy;
    let eq_q_xy_q_az = eq::symmetry(quality::to_eq(q_az_q_xy));
    let x2_q_az = imply::in_right_arg(x2_q_xy, eq_q_xy_q_az.clone());
    let pord_x2_q_az = pord_x2_q_xy.by_eq_right(eq_q_xy_q_az);
    (x2_q_az, pord_x2_q_az)
}

/// Get the type of the path between paths.
pub fn h2<X: Prop, Y: Prop, X2: Prop, Y2: Prop, N: Nat, A: HProp<S<S<N>>>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
    ty_x2_q_xy: Ty<X2, Q<X, Y>>,
    ty_y2_q_xy: Ty<Y2, Q<X, Y>>,
) -> Q<H2<A, N>, Q<X2, Y2>> {
    let ty_x2_q_az = univalence::lift_ty(ty_x.clone(), ty_y.clone(), ty_x2_q_xy);
    let ty_y2_q_az = univalence::lift_ty(ty_x, ty_y, ty_y2_q_xy);
    A::H::hn(ty_x2_q_az, ty_y2_q_az)
}
