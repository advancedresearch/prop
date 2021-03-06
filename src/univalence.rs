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
use qubit::Qubit;
use nat::{EqNat, Dec, Lt, Nat, S, Z};
use path_semantics::{Ty, LProp};

pub use hom_eq_commute as hom_eq_symmetry;

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

/// Implemented by homotopy equivalences.
///
/// This is a partial equivalence relation.
pub trait HomotopyEquivalence<A: Prop, B: Prop>: Prop {
    /// The associated homotopy level.
    type N: HLev;
    /// Relation constructor.
    type Rel<A2: Prop, B2: Prop>: HomotopyEquivalence<A2, B2, N = Self::N>;
    /// `hom_eq(n, a, b) ??? hom_eq(n, b, c) => hom_eq(n, a, c)`.
    fn transitivity<C: Prop>(self, other: Self::Rel<B, C>) -> Self::Rel<A, C>;
    /// `hom_eq(n, a, b) => hom_eq(n, b, a)`.
    fn symmetry(self) -> Self::Rel<B, A>;

    /// Cast to self.
    fn cast<A2: Prop, B2: Prop>(
        _: <<Self::N as HLev>::Out<A2, B2> as HomotopyEquivalence<A2, B2>>::Rel<A, B>
    ) -> Self;
    /// Cast to other.
    fn cast_lift<A2: Prop, B2: Prop>(
        self
    ) -> <<Self::N as HLev>::Out<A2, B2> as HomotopyEquivalence<A2, B2>>::Rel<A, B>;
}

/// Implemented by homotopy equalities.
///
/// This is a total equivalence relation.
pub trait HomotopyEquality<A: Prop>: HomotopyEquivalence<A, A> {
    /// `hom_eq(n, a, a)`.
    fn refl() -> Self;
}

/// Implemented by homotopy levels.
pub trait HLev: Nat {
    /// The output type.
    type Out<A: Prop, B: Prop>: HomotopyEquivalence<A, B, N = Self>;
}

impl HLev for Z {
    type Out<A: Prop, B: Prop> = True;
}
impl<X: HLev> HLev for S<X> {
    type Out<A: Prop, B: Prop> = And<Eq<Qubit<X, A>, Qubit<X, B>>, <X as HLev>::Out<A, B>>;
}

impl<A: Prop, B: Prop> HomotopyEquivalence<A, B> for True {
    type N = Z;
    type Rel<A2: Prop, B2: Prop> = True;
    fn transitivity<C: Prop>(self, _: True) -> True {True}
    fn symmetry(self) -> True {True}

    fn cast<A2: Prop, B2: Prop>(_: True) -> True {True}
    fn cast_lift<A2: Prop, B2: Prop>(self) -> True {True}
}

impl<A: Prop> HomotopyEquality<A> for True {
    fn refl() -> Self {True}
}

impl<A: Prop, B: Prop, X: HLev> HomotopyEquivalence<A, B>
for And<Eq<Qubit<X, A>, Qubit<X, B>>, <X as HLev>::Out<A, B>> {
    type N = S<X>;
    type Rel<A2: Prop, B2: Prop> = And<Eq<Qubit<X, A2>, Qubit<X, B2>>, <X as HLev>::Out<A2, B2>>;
    fn transitivity<C: Prop>(self, other: Self::Rel<B, C>) -> Self::Rel<A, C> {
        (
            eq::transitivity(self.0, other.0),
            HomotopyEquivalence::cast(self.1.transitivity::<C>(HomotopyEquivalence::cast_lift(other.1)))
        )
    }
    fn symmetry(self) -> Self::Rel<B, A> {
        (
            eq::symmetry(self.0),
            HomotopyEquivalence::cast(self.1.symmetry())
        )
    }

    fn cast<A2: Prop, B2: Prop>(arg: Self) -> Self {arg}
    fn cast_lift<A2: Prop, B2: Prop>(self) -> Self {self}
}

impl<A: Prop, X: HLev> HomotopyEquality<A>
for And<Eq<Qubit<X, A>, Qubit<X, A>>, <X as HLev>::Out<A, A>>
    where <X as HLev>::Out<A, A>: HomotopyEquality<A>
{
    fn refl() -> Self {
        (
            eq::refl(),
            HomotopyEquality::refl()
        )
    }
}

/// Homotopy equality of level `N`.
pub type HomEq<N, A, B> = <N as HLev>::Out<A, B>;
/// Homotopy equality of level 2.
pub type HomEq2<A, B> = HomEq<S<S<Z>>, A, B>;

/// `hom_eq(n, a, b) ??? hom_eq(n, b, c) => hom_eq(n, a, c)`.
pub fn hom_eq_transitivity<N: HLev, A: Prop, B: Prop, C: Prop>(
    ab: HomEq<N, A, B>,
    bc: HomEq<N, B, C>,
) -> HomEq<N, A, C> {
    HomotopyEquivalence::cast(ab.transitivity(HomotopyEquivalence::cast_lift(bc)))
}

/// `hom_eq(n, a, b) => hom_eq(n, b, a)`.
pub fn hom_eq_commute<N: HLev, A: Prop, B: Prop>(ab: HomEq<N, A, B>) -> HomEq<N, B, A> {
    HomotopyEquivalence::cast(ab.symmetry())
}

/// `hom_eq(n, a, a)`.
pub fn hom_eq_refl<N: HLev, A: Prop>() -> HomEq<N, A, A>
    where HomEq<N, A, A>: HomotopyEquality<A>
{
    HomotopyEquality::refl()
}

/// `(a ~~ b) => hom_eq(2, a, b)`.
pub fn q_to_hom_eq_2<A: Prop, B: Prop>(q: Q<A, B>) -> HomEq2<A, B> {
    to_hom_eq_2(quality::to_eq(q.clone()), quality::to_eq_q(q))
}

/// `(a == b) ??? ((a ~~ a) == (b ~~ b)) => hom_eq(2, a, b)`.
pub fn to_hom_eq_2<A: Prop, B: Prop>(
    eq: Eq<A, B>,
    eq_q: Eq<Q<A, A>, Q<B, B>>
) -> HomEq2<A, B> {
    (qubit::from_eq_q(eq_q), (qubit::from_eq(eq), True))
}

/// `hom_eq(2, a, b) => (a == b) ??? ((a ~~ b) == (b ~~ b))`.
pub fn from_hom_eq_2<A: Prop, B: Prop>(
    hom_eq: HomEq2<A, B>
) -> And<Eq<A, B>, Eq<Q<A, A>, Q<B, B>>> {
    (qubit::to_eq(hom_eq.1.0), qubit::to_eq_q(hom_eq.0))
}

/// Homotopy Level.
///
/// For theoretical background, see [nLab - homotopy levels](https://ncatlab.org/nlab/show/homotopy+level).
pub trait HomotopyLevel<N: Nat>: Prop {
    /// A type such that it proves homotopy level 0.
    type H0: Prop;
    /// A type such that it proves a lower homotopy level.
    type H: HomotopyLevel<<N as Dec>::Out>;
    /// Homotopy level 0.
    fn h0<Y: LProp>(ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat;
    /// Higher homotopy level.
    fn hn<X: LProp, Y: LProp>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>;
}

/// Decidable Homotopy Level.
///
/// Same as Homotopy Level, but for decidable propositions.
pub trait DecidableHomotopyLevel<N: Nat>: DProp {
    /// A type such that it proves homotopy level 0.
    type H0: DProp;
    /// A type such that it proves a lower homotopy level.
    type H: DecidableHomotopyLevel<<N as Dec>::Out>;
    /// Homotopy level 0.
    fn h0<Y: LProp>(ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat;
    /// Higher homotopy level.
    fn hn<X: LProp, Y: LProp>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>;
}

impl<N: Nat, T: DecidableHomotopyLevel<N>> HomotopyLevel<N> for T {
    type H0 = <T as DecidableHomotopyLevel<N>>::H0;
    type H = <T as DecidableHomotopyLevel<N>>::H;
    fn h0<Y: LProp>(ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat {
        <T as DecidableHomotopyLevel<N>>::h0(ty_y)
    }
    fn hn<X: LProp, Y: LProp>(
        ty_x: Ty<X, Self>,
        ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N> {
        <T as DecidableHomotopyLevel<N>>::hn(ty_x, ty_y)
    }
}

impl<N: Nat> DecidableHomotopyLevel<N> for True {
    type H0 = True;
    type H = True;
    fn h0<Y: LProp>(_ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat
    {
        unimplemented!()
    }
    fn hn<X: LProp, Y: LProp>(
        _ty_x: Ty<X, Self>,
        _ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>
    {
        unimplemented!()
    }
}

impl<N: Nat> DecidableHomotopyLevel<S<N>> for False {
    type H0 = True;
    type H = True;
    fn h0<Y: LProp>(_ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (S<N>, Z): EqNat {
        unimplemented!()
    }
    fn hn<X: LProp, Y: LProp>(
        _ty_x: Ty<X, Self>,
        _ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<S<N>>
    {
        unimplemented!()
    }
}

impl<N: Nat> DecidableHomotopyLevel<N> for Or<True, True> {
    type H0 = Or<True, True>;
    type H = Or<True, True>;
    fn h0<Y: LProp>(ty_y_self: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat
    {
        let eq_self_true: Eq<Self, True> = (True.map_any(), Left(True).map_any());
        let ty_y_true = path_semantics::ty_in_right_arg(ty_y_self, eq_self_true.clone());
        let q_trueh0_y = <True as DecidableHomotopyLevel<N>>::h0(ty_y_true);
        quality::in_left_arg(q_trueh0_y, eq::symmetry(eq_self_true))
    }
    fn hn<X: LProp, Y: LProp>(
        ty_x_self: Ty<X, Self>,
        ty_y_self: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>
    {
        let eq_self_true: Eq<Self, True> = (True.map_any(), Left(True).map_any());
        let ty_x_true = path_semantics::ty_in_right_arg(ty_x_self, eq_self_true.clone());
        let ty_y_true = path_semantics::ty_in_right_arg(ty_y_self, eq_self_true.clone());
        let q_selfh_q_x_y = <True as DecidableHomotopyLevel<N>>::hn(ty_x_true, ty_y_true);
        quality::in_left_arg(q_selfh_q_x_y, eq::symmetry(eq_self_true))
    }
}

impl<N: Nat> DecidableHomotopyLevel<N> for Or<True, False> {
    type H0 = Or<True, False>;
    type H = Or<True, False>;
    fn h0<Y: LProp>(ty_y_self: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (N, Z): EqNat
    {
        let eq: Eq<True, Or<True, False>> = (Left(True).map_any(), True.map_any());
        let ty_y_true = path_semantics::ty_in_right_arg(ty_y_self, eq::symmetry(eq.clone()));
        let q_trueh_y = <True as HomotopyLevel<N>>::h0(ty_y_true);
        quality::in_left_arg(q_trueh_y, eq)
    }
    fn hn<X: LProp, Y: LProp>(
        ty_x_self: Ty<X, Self>,
        ty_y_self: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<N>
    {
        let eq: Eq<True, Or<True, False>> = (Left(True).map_any(), True.map_any());
        let ty_x_true = path_semantics::ty_in_right_arg(ty_x_self, eq::symmetry(eq.clone()));
        let ty_y_true = path_semantics::ty_in_right_arg(ty_y_self, eq::symmetry(eq.clone()));
        let q_trueh_x_y = <True as HomotopyLevel<N>>::hn(ty_x_true, ty_y_true);
        quality::in_left_arg(q_trueh_x_y, eq)
    }
}

/// Represents a Set of homotopy level 2.
#[derive(Clone)]
pub struct Set;

impl<N: Nat> HomotopyLevel<S<S<N>>> for Set {
    type H0 = True;
    type H = Or<True, False>;
    fn h0<Y: LProp>(_ty_y: Ty<Y, Self>) -> Q<Self::H0, Y>
        where (S<S<N>>, Z): EqNat {
        unimplemented!()
    }
    fn hn<X: LProp, Y: LProp>(
        _ty_x: Ty<X, Self>,
        _ty_y: Ty<Y, Self>
    ) -> Q<Self::H, Q<X, Y>>
        where Z: Lt<S<S<N>>>
    {
        unimplemented!()
    }
}

/// Shorthand for homotopy proposition.
pub trait HProp<N: Nat>: HomotopyLevel<N> {}
impl<N: Nat, T: HomotopyLevel<N>> HProp<N> for T {}

/// Lower homotopy level with 2.
pub type H2<A, N> = <<A as HomotopyLevel<S<S<N>>>>::H as HomotopyLevel<S<N>>>::H;

/// `(x : a) => (a::h0 : a)`.
pub fn ty_h0<X: LProp, A: HProp<Z>>(ty_x_a: Ty<X, A>) -> Ty<A::H0, A> {
    let q_h0_x = A::h0(ty_x_a.clone());
    let eq_x_h0 = eq::symmetry(quality::to_eq(q_h0_x));
    path_semantics::ty_in_left_arg(ty_x_a, eq_x_h0)
}

/// Proves that homotopy level 0 has quality between any members.
pub fn h0_q<X: LProp, Y: LProp, A: HProp<Z>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
) -> Q<X, Y> {
    let q_zx = A::h0(ty_x);
    let q_zy = A::h0(ty_y);
    let q_xz = quality::symmetry(q_zx);
    quality::transitivity(q_xz, q_zy)
}

/// Proves that homotopy level 1 or higher has quality between self-quality of any members.
pub fn h1_q2<X: LProp, Y: LProp, N: Nat, A: HProp<S<N>>>(
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
pub fn lift_ty<X: LProp, Y: LProp, X2: Prop, N: Nat, A: HProp<S<N>>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
    ty_x2_q_xy: Ty<X2, Q<X, Y>>,
) -> Ty<X2, A::H> {
    let q_az_q_xy = A::hn(ty_x, ty_y);
    let eq_q_xy_q_az = eq::symmetry(quality::to_eq(q_az_q_xy));
    path_semantics::ty_in_right_arg(ty_x2_q_xy, eq_q_xy_q_az)
}

/// Get the type of the path between paths.
pub fn h2<X: LProp, Y: LProp, X2: LProp, Y2: LProp, N: Nat, A: HProp<S<S<N>>>>(
    ty_x: Ty<X, A>,
    ty_y: Ty<Y, A>,
    ty_x2_q_xy: Ty<X2, Q<X, Y>>,
    ty_y2_q_xy: Ty<Y2, Q<X, Y>>,
) -> Q<H2<A, N>, Q<X2, Y2>> {
    let ty_x2_q_az = univalence::lift_ty(ty_x.clone(), ty_y.clone(), ty_x2_q_xy);
    let ty_y2_q_az = univalence::lift_ty(ty_x, ty_y, ty_y2_q_xy);
    A::H::hn(ty_x2_q_az, ty_y2_q_az)
}

/// `(x : set) ??? (y : set) ??? (x2 : (x ~~ y)) ??? (y2 : (x ~~ y))  =>  (x2 ~~ y2)`.
pub fn set_h2<X: LProp, Y: LProp, X2: LProp, Y2: LProp>(
    ty_x: Ty<X, Set>,
    ty_y: Ty<Y, Set>,
    ty_x2_q_xy: Ty<X2, Q<X, Y>>,
    ty_y2_q_xy: Ty<Y2, Q<X, Y>>,
) -> Q<X2, Y2> {
    let q_tr_q_x2_y2 = h2::<X, Y, X2, Y2, S<S<Z>>, Set>(ty_x, ty_y, ty_x2_q_xy, ty_y2_q_xy);
    quality::to_eq(q_tr_q_x2_y2).0(Left(True))
}

/// `(x : set) ??? (y : set) => ((x ??? y) : set)`
pub fn set_and<X: LProp, Y: LProp>(
    ty_x: Ty<X, Set>,
    ty_y: Ty<Y, Set>
) -> Ty<And<X, Y>, Set> {
    let eq: Eq<And<Set, Set>, Set> = (Set.map_any(),(Set, Set).map_any());
    path_semantics::ty_in_right_arg(path_semantics::ty_and(ty_x, ty_y), eq)
}

/// `(x : set) ??? (y : set) => ((x ??? y) : set)`.
pub fn set_or<X: LProp, Y: LProp>(
    ty_x: Ty<X, Set>,
    ty_y: Ty<Y, Set>
) -> Ty<Or<X, Y>, Set> {
    let eq: Eq<Or<Set, Set>, Set> = (Set.map_any(), Left(Set).map_any());
    path_semantics::ty_in_right_arg(path_semantics::ty_or(ty_x, ty_y), eq)
}

/// `(x : a) ??? (x : b)  =>  (a ~~ b)` when `a` and `b` are homotopy level 0.
pub fn h0_ext<A: HProp<Z>, B: HProp<Z>, X: LProp>(
    ty_xa: Ty<X, A>,
    ty_xb: Ty<X, B>,
) -> Q<A, B> {
    let q_ah0_x = A::h0(ty_xa.clone());
    let q_bh0_x = B::h0(ty_xb.clone());
    let q_x_bh0 = quality::symmetry(q_bh0_x.clone());
    let q_ah0_bh0 = quality::transitivity(q_ah0_x.clone(), q_x_bh0);

    let eq_x_ah0 = eq::symmetry(quality::to_eq(q_ah0_x));
    let eq_x_bh0 = eq::symmetry(quality::to_eq(q_bh0_x));
    let ty_ah0_a = path_semantics::ty_in_left_arg(ty_xa, eq_x_ah0);
    let ty_bh0_b = path_semantics::ty_in_left_arg(ty_xb, eq_x_bh0);
    let psem = path_semantics::assume();
    psem(((q_ah0_bh0, (ty_ah0_a.1, ty_bh0_b.1)), (ty_ah0_a.0, ty_bh0_b.0)))
}

/// `(x : a) ??? (x : b) ??? ((x ~~ x) == x)  =>  (a ~~ b)`
/// when `a` and `b` are homotopy level 1 or larger.
pub fn h1_lim_ext<A: HProp<S<N>>, B: HProp<S<N>>, X: LProp, N: Nat>(
    ty_xa: Ty<X, A>,
    ty_xb: Ty<X, B>,
    q_xx_x: Eq<Q<X, X>, X>,
) -> Q<A, B> {
    let q_ah_x = A::hn(ty_xa.clone(), ty_xa.clone());
    let q_bh_x = B::hn(ty_xb.clone(), ty_xb.clone());
    let q_x_bh = quality::symmetry(q_bh_x.clone());
    let q_ah_bh = quality::transitivity(q_ah_x.clone(), q_x_bh);

    let eq_q_xx_ah = eq::symmetry(quality::to_eq(q_ah_x));
    let eq_q_xx_bh = eq::symmetry(quality::to_eq(q_bh_x));
    let eq_x_ah = eq::in_left_arg(eq_q_xx_ah, q_xx_x.clone());
    let eq_x_bh = eq::in_left_arg(eq_q_xx_bh, q_xx_x);
    let ty_ah_a = path_semantics::ty_in_left_arg(ty_xa, eq_x_ah);
    let ty_bh_b = path_semantics::ty_in_left_arg(ty_xb, eq_x_bh);
    let psem = path_semantics::assume();
    psem(((q_ah_bh, (ty_ah_a.1, ty_bh_b.1)), (ty_ah_a.0, ty_bh_b.0)))
}

/// `(x : a) ??? (x : true) => a`.
pub fn h0_true<X: LProp, A: HProp<Z>>(
    ty_x_a: Ty<X, A>,
    ty_x_true: Ty<X, True>,
) -> A {
    quality::to_eq(h0_ext(ty_x_a, ty_x_true)).1(True)
}

/// `(x : a) => a`.
pub fn h0<X: LProp, A: HProp<Z>>(ty_x_a: Ty<X, A>) -> A
    where X::N: Nat
{
    h0_true(ty_x_a, path_semantics::ty_true())
}

/// `(x : a) ??? (x : false) ??? ((x ~~ x) == x)  =>  ??a`.
pub fn h1_false<X: LProp, N: Nat, A: HProp<S<N>>>(
    ty_x_a: Ty<X, A>,
    ty_x_false: Ty<X, False>,
    q: Eq<Q<X, X>, X>,
) -> Not<A> {
    quality::to_eq(univalence::h1_lim_ext(ty_x_a, ty_x_false, q)).0
}

/// `(x : a) ??? (x : true) ??? ((x ~~ x) == x)  =>  a`.
pub fn h1_true<X: LProp, N: Nat, A: HProp<S<N>>>(
    ty_x_a: Ty<X, A>,
    ty_x_true: Ty<X, True>,
    q: Eq<Q<X, X>, X>,
) -> A {
    quality::to_eq(univalence::h1_lim_ext(ty_x_a, ty_x_true, q)).1(True)
}

/// `(x : true) => (true ~~ x)`.
pub fn h0_q_true<X: LProp>(ty_x: Ty<X, True>) -> Q<True, X> {
    <True as HomotopyLevel<Z>>::h0(ty_x)
}

/// `(x : true) => (x ~~ x)`.
pub fn h0_true_q<X: LProp>(ty_x: Ty<X, True>) -> Q<X, X> {
    let f = h0_q_true(ty_x);
    quality::transitivity(quality::symmetry(f.clone()), f)
}

/// `(x : false)  =>  (x ~~ x)`.
pub fn h1_false_q<X: LProp>(ty_x_false: Ty<X, False>) -> Q<X, X> {
    quality::to_eq(<False as HomotopyLevel<S<Z>>>::hn(ty_x_false.clone(), ty_x_false)).0(True)
}

/// `(x : true) => x`.
pub fn h0_lproof<X: LProp>(ty_x: Ty<X, True>) -> X {
    quality::to_eq(h0_q_true(ty_x)).0(True)
}

/// `(x : true) => ((x ~~ x) == x)`.
pub fn h0_lim<X: LProp>(ty_x: Ty<X, True>) -> Eq<Q<X, X>, X> {
    (h0_lproof(ty_x.clone()).map_any(), h0_true_q(ty_x).map_any())
}

/// `(x : true) => ((x ~~ x) ~~ x)`.
pub fn h0_qlim<X: LProp>(ty_x: Ty<X, True>) -> Q<Q<X, X>, X> {
    let lim = h0_lim(ty_x.clone());
    let ty_q = path_semantics::ty_in_left_arg(ty_x, eq::symmetry(lim.clone()));
    let qq = h0_true_q(ty_q);
    quality::in_right_arg(qq, lim)
}

/// `(x : true) ??? (x : false)  =>  (true ~~ false)`.
pub fn q_contradict<X: LProp>(
    ty_x_true: Ty<X, True>,
    ty_x_false: Ty<X, False>
) -> Q<True, False> {
    h1_lim_ext::<True, False, X, S<Z>>(ty_x_true.clone(), ty_x_false, h0_lim(ty_x_true))
}

/// `(x : true) ??? (x : false)  =>  false`.
pub fn contradict<X: LProp>(
    ty_x_true: Ty<X, True>,
    ty_x_false: Ty<X, False>
) -> False {
    quality::to_eq(q_contradict(ty_x_true, ty_x_false)).0(True)
}

/// `(x : a) ??? ((x ~~ x) == x)  =>  (a ??? ??a) == ((x : true) ??? (x : false))`.
pub fn h1_lim_excm<X: LProp, N: Nat, A: HProp<S<N>>>(
    ty_x_a: Ty<X, A>,
    lim: Eq<Q<X, X>, X>,
) -> Eq<ExcM<A>, Or<Ty<X, True>, Ty<X, False>>> {
    let ty_x_a_clone = ty_x_a.clone();
    (
        Rc::new(move |excm| match excm {
            Left(a) => Left(path_semantics::ty_triv(ty_x_a_clone.clone(), a)),
            Right(na) => Right(path_semantics::ty_non_triv(ty_x_a_clone.clone(), na)),
        }),
        Rc::new(move |or| match or {
            Left(ty_x_true) => Left(h1_true(ty_x_a.clone(), ty_x_true, lim.clone())),
            Right(ty_x_false) => Right(h1_false(ty_x_a.clone(), ty_x_false, lim.clone())),
        })
    )
}

/// `(x : a) ??? ((x ~~ x) == x)  =>  (x : true) ??? (x : false)`.
pub fn h1_lim_excm_da<X: LProp, N: Nat, A: DProp + HProp<S<N>>>(
    ty_x_a: Ty<X, A>,
    lim: Eq<Q<X, X>, X>,
) -> Or<Ty<X, True>, Ty<X, False>> {
    h1_lim_excm(ty_x_a, lim).0(A::decide())
}

/// `(x : false) ??? ((x ~~ x) == x)  =>  false`.
pub fn h1_false_lim_contradict<X: LProp>(
    ty_x_false: Ty<X, False>,
    lim: Eq<Q<X, X>, X>
) -> False {
    ty_x_false.0(lim.0(h1_false_q(ty_x_false.clone())))
}

/// `(x : a) ??? ((x ~~ x) == x) ??? (a ??? ??a)  =>  (x : true)`.
pub fn h1_lim_excm_true<X: LProp, N: Nat, A: HProp<S<N>>>(
    ty_x_a: Ty<X, A>,
    lim: Eq<Q<X, X>, X>,
    excm: Or<A, Not<A>>,
) -> Ty<X, True> {
    match h1_lim_excm(ty_x_a, lim.clone()).0(excm) {
        Left(ty_x_true) => ty_x_true,
        Right(ty_x_false) => imply::absurd()(h1_false_lim_contradict(ty_x_false, lim)),
    }
}
