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
use nat::{Nat, S, Z};
use path_semantics::{Ty, LProp};

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
pub fn eq_lift<A: Prop, B: Prop>(_eq_eq_q: Eq<Eq<A, B>, Q<A, B>>) -> Univ<A, B> {
    unimplemented!()
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
    /// `hom_eq(n, a, b) ⋀ hom_eq(n, b, c) => hom_eq(n, a, c)`.
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

/// `hom_eq(n, a, b) ⋀ hom_eq(n, b, c) => hom_eq(n, a, c)`.
pub fn hom_eq_transitivity<N: HLev, A: Prop, B: Prop, C: Prop>(
    ab: HomEq<N, A, B>,
    bc: HomEq<N, B, C>,
) -> HomEq<N, A, C> {
    HomotopyEquivalence::cast(ab.transitivity(HomotopyEquivalence::cast_lift(bc)))
}

/// `hom_eq(n, a, b) => hom_eq(n, b, a)`.
pub fn hom_eq_symmetry<N: HLev, A: Prop, B: Prop>(ab: HomEq<N, A, B>) -> HomEq<N, B, A> {
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

/// `(a == b) ⋀ ((a ~~ a) == (b ~~ b)) => hom_eq(2, a, b)`.
pub fn to_hom_eq_2<A: Prop, B: Prop>(
    eq: Eq<A, B>,
    eq_q: Eq<Q<A, A>, Q<B, B>>
) -> HomEq2<A, B> {
    (qubit::from_eq_q(eq_q), (qubit::from_eq(eq), True))
}

/// `hom_eq(2, a, b) => (a == b) ⋀ ((a ~~ b) == (b ~~ b))`.
pub fn from_hom_eq_2<A: Prop, B: Prop>(
    hom_eq: HomEq2<A, B>
) -> And<Eq<A, B>, Eq<Q<A, A>, Q<B, B>>> {
    (qubit::to_eq(hom_eq.1.0), qubit::to_eq_q(hom_eq.0))
}

/// Homotopy Level.
///
/// For theoretical background, see [nLab - homotopy levels](https://ncatlab.org/nlab/show/homotopy+level).
pub trait HomotopyLevel0<A: Prop, B: Prop>: HomotopyEquivalence<A, B, N = Z> {
    /// A type such that it proves homotopy level 0.
    type H0: Prop;
    /// Homotopy level 0.
    fn h0<X: LProp>(ty_x: Ty<X, Self>) -> HomEq<Z, Self::H0, X>;
}

impl<A: Prop, B: Prop> HomotopyLevel0<A, B> for True {
    type H0 = True;
    fn h0<X: LProp>(_ty_x: Ty<X, Self>) -> HomEq<Z, True, X> {
        True
    }
}
