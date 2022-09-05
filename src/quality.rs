//! # Path Semantical Quality
//!
//! Path Semantical Quality is a partial equivalence relation that lifts biconditions
//! with symbolic distinction.
//! See [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/path-semantical-quality.pdf).
//!
//! For a different implementation of quality, see [PSI in Avalog](https://github.com/advancedresearch/avalog/blob/master/source/psi.txt).
//!
//! There is also an implementation in [Pocket-Prover](https://github.com/advancedresearch/pocket_prover).
//!
//! ### Work-around for symbolic distinction
//!
//! IPL does not support symbolic distinction, so quality must be assumed explicitly.
//!
//! ### Lifting equality into quality
//!
//! `EqQ<A, B>`
//!
//! This implementation lifts equality directly to quality.
//! Since this is unsound without symbolic distinction,
//! it is not possible to assume this directly.
//!
//! Although IPL does not support symbolic distinction,
//! one can use `EqQ<A, B>` (`(a == b) => (a ~~ b)`) to model symbolic distinction.
//! This means `EqQ<A, B>` can be used as an assumption that `A` and `B` are symbolic distinct.
//!
//! ### Seshatism vs Platonism
//!
//! [Seshatism](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf)
//! is a way to reject two forms of Platonism:
//!
//! - `¬(a ~~ a)`: Seshatism
//! - `a ~~ a`: Platonism 1 (Loop Witness)
//! - `a ~~ b`: Platonism 2 (Product Witness)
//!
//! Since `a ~~ b` implies `a ~~ a`, both Loop and Product Witness are rejected by Seshatism.
//!
//! ### Seshatic Relations
//!
//! `Seshatic<A, B>`
//!
//! When a relation `p(a, b)` is Seshatic,
//! it means that it implies Seshatism of either `a` or `b`:
//!
//! `p(a, b) => ¬(a ~~ a) ⋁ ¬(b ~~ b)`
//!
//! ### Pure Platonism
//!
//! `PurePlatonism<A, B>` (feature flag is not needed)
//!
//! Feature flag: "pure_platonism" (for convenience functions)
//!
//! Pure Platonism is not strong enough to prove quality,
//! but can prove `False` from Seshatism (`Not<Q<A, A>>`).
//! Can be used when reasoning about Seshatism is not needed.
//!
//! This implementation uses a 2-avatar of equality
//! to model quality within IPL,
//! by exploiting the property `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
//!
//! IPL does not have symbolic distinction,
//! so equality `a == b` can not be lifted properly into `a ~~ b`.
//! However, since quality is not decidable within IPL,
//! one can not prove `a ~~ b` from `¬¬(a ~~ b)`.
//! This means that the 2-avatar can hide reflexivity,
//! by lifting `a == b` to `(a ~~ b) ⋁ ¬¬(a ~~ b)`.
//!
//! Notice that this implementation does not support reasoning about Seshatism,
//! because `¬(a ~~ a)` (Seshatism) is absurd in this model (it proves anything).
//! Proper Seshatism requires quality to use symbolic distinction instead of the trick above.
//!
//! Interpreted as an [Avatar Graph](https://advancedresearch.github.io/avatar-extensions/summary.html#avatar-graphs),
//! the core is `a == b` and there are two 1-avatars:
//!
//! - `(a ~~ b)`
//! - `¬¬(a ~~ b)`
//!
//! The 2-avatar integrates `(a ~~ b)` and `¬¬(a ~~ b)` using `⋁`.
//!
//! ### Aquality
//!
//! Aquality is a Seshatic relation that is symmetric to quality.
//!
//! One can think about aquality vs quality as a perspective
//! where Seshatism and Platonism becomes mirror images of each other.
//!
//! The core axiom biases mathematics toward Platonism,
//! but this choice is arbitrary since `¬~x == ~¬x`.
//! Therefore, "Platonism" is whatever theory/philosophy
//! that is associated with the quality/aquality used in a core axiom.
//! The dual theory/philosophy is Seshatism.
//!
//! Dualities of this form is common in mathematics,
//! so Seshatism vs Platonism is often used to talk about analogues of other dualities as well.

use crate::*;

use univalence::HomEq2;
use qubit::Qu;

/// Lifts equality into quality.
pub type EqQ<A, B> = Imply<Eq<A, B>, Q<A, B>>;
/// Lifts equality into aquality.
pub type EqAq<A, B> = Imply<Eq<A, B>, Aq<A, B>>;
/// Pure Platonism assumption.
pub type PurePlatonism<A, B> = Imply<Eq<A, B>, Or<Q<A, B>, Not<Not<Q<A, B>>>>>;
/// A Seshatic relation `¬(a ~~ a) ⋁ ¬(b ~~ b)`.
pub type Seshatic<A, B> = Or<Not<Q<A, A>>, Not<Q<B, B>>>;

/// Prevents other qualities of `A` from excluding `B`.
pub trait NoOtherQ<A, B>: 'static + Clone {
    /// `(a ~~ c) => ¬¬(b ~~ c)`.
    fn no_other_q<C: Prop>(&self, q: Q<A, C>) -> Not<Not<Q<B, C>>>;
}

/// If something is qual to `A`, then `A` is qual to `B`.
pub trait UniqQ<A, B>: NoOtherQ<A, B> {
    /// `(a ~~ a) => (a ~~ b)`.
    fn uniq_q(&self, q_aa: Q<A, A>) -> Q<A, B>;
}

/// Maps every true proposition `a` into self-quality `a ~~ a`.
pub trait IdQ: 'static + Clone {
    /// `a => (a ~~ a)`.
    fn idq<A: Prop>(&self, a: A) -> Q<A, A>;
    /// `¬(a ~~ a) => ¬a`
    fn sesh_to_not<A: Prop>(&self, sesh_a: Not<Q<A, A>>) -> Not<A> {
        let copy = self.clone();
        imply::modus_tollens(Rc::new(move |a| copy.idq(a)))(sesh_a)
    }
}

/// Maps every self-quality `a ~~ a` into true proposition `a`.
pub trait QId: 'static + Clone {
    /// `(a ~~ a) => a`.
    fn qid<A: Prop>(&self, q_aa: Q<A, A>) -> A;
    /// `¬a => ¬(a ~~ a)`.
    fn not_to_sesh<A: Prop>(&self, na: Not<A>) -> Not<Q<A, A>> {
        let copy = self.clone();
        imply::modus_tollens(Rc::new(move |q_aa| copy.qid(q_aa)))(na)
    }
}

/// Quality definition `(a ~~ b) == ((a == b) ⋀ ~a ⋀ ~b)`.
pub type Q<A, B> = And<Eq<A, B>, And<Qu<A>, Qu<B>>>;

/// Aquality definition `(a ~¬~ b) == ((a == b) ⋀ ~¬a ⋀ ~¬b)`.
pub type Aq<A, B> = And<Eq<A, B>, And<Qu<Not<A>>, Qu<Not<B>>>>;

/// Symmetry `(a ~~ b) => (b ~~ a)`.
pub fn symmetry<A: Prop, B: Prop>((eq, and_qu): Q<A, B>) -> Q<B, A> {
    (eq::symmetry(eq), and::symmetry(and_qu))
}

/// Symmetry `(a ~¬~ b) => (b ~¬~ a)`.
pub fn aq_symmetry<A: Prop, B: Prop>((eq, and_qu): Aq<A, B>) -> Aq<B, A> {
    (eq::symmetry(eq), and::symmetry(and_qu))
}

/// Negated symmetry `¬(a ~~ b) => ¬(b ~~ a)`.
pub fn nq_symmetry<A: Prop, B: Prop>(nq: Not<Q<A, B>>) -> Not<Q<B, A>> {
    Rc::new(move |q| nq(symmetry(q)))
}

/// Negated symmetry `¬(a ~¬~ b) => ¬(b ~¬~ a)`.
pub fn naq_symmetry<A: Prop, B: Prop>(naq: Not<Aq<A, B>>) -> Not<Aq<B, A>> {
    Rc::new(move |q| naq(aq_symmetry(q)))
}

/// Transitivity `(a ~~ b) ⋀ (b ~~ c) => (a ~~ c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, _)): Q<A, B>,
    (eq_bc, (_, qu_c)): Q<B, C>
) -> Q<A, C> {
    (eq::transitivity(eq_ab, eq_bc), (qu_a, qu_c))
}

/// Transitivity `(a ~¬~ b) ⋀ (b ~¬~ c) => (a ~¬~ c)`.
pub fn aq_transitivity<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, _)): Aq<A, B>,
    (eq_bc, (_, qu_c)): Aq<B, C>
) -> Aq<A, C> {
    (eq::transitivity(eq_ab, eq_bc), (qu_a, qu_c))
}

/// `(a ~~ b) ⋀ ¬(a ~~ c) => ¬(b ~~ c)`.
pub fn nq_left<A: Prop, B: Prop, C: Prop>(
    q_ab: Q<A, B>,
    sesh_ac: Not<Q<A, C>>
) -> Not<Q<B, C>> {
    Rc::new(move |q_bc| sesh_ac(transitivity(q_ab.clone(), q_bc)))
}

/// `(a ~¬~ b) ⋀ ¬(a ~¬~ c) => ¬(b ~¬~ c)`.
pub fn naq_left<A: Prop, B: Prop, C: Prop>(
    q_ab: Aq<A, B>,
    sesh_ac: Not<Aq<A, C>>
) -> Not<Aq<B, C>> {
    Rc::new(move |q_bc| sesh_ac(aq_transitivity(q_ab.clone(), q_bc)))
}

/// `(a ~~ b) ⋀ ¬(b ~~ c) => ¬(a ~~ c)`.
pub fn nq_right<A: Prop, B: Prop, C: Prop>(
    q_ab: Q<A, B>,
    sesh_bc: Not<Q<B, C>>
) -> Not<Q<A, C>> {
    Rc::new(move |q_ac| sesh_bc(transitivity(symmetry(q_ab.clone()), q_ac)))
}

/// `(a ~¬~ b) ⋀ ¬(b ~¬~ c) => ¬(a ~¬~ c)`.
pub fn naq_right<A: Prop, B: Prop, C: Prop>(
    q_ab: Aq<A, B>,
    sesh_bc: Not<Aq<B, C>>
) -> Not<Aq<A, C>> {
    Rc::new(move |q_ac| sesh_bc(aq_transitivity(aq_symmetry(q_ab.clone()), q_ac)))
}

/// Equality maybe lift `(a == b) => ( (a ~~ b) ⋁ true )`.
pub fn eq_maybe_lift<A: Prop, B: Prop>(_: Eq<A, B>) -> Or<Q<A, B>, True> {
    Right(True)
}

/// Equality lift `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
#[cfg(feature = "pure_platonism")]
pub fn assume_pure_platonism<A: Prop, B: Prop>() -> PurePlatonism<A, B> {
    Rc::new(move |eq| eq_lift(eq))
}

/// Equality lift `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
#[cfg(feature = "pure_platonism")]
pub fn eq_lift<A: Prop, B: Prop>(_: Eq<A, B>) -> Or<Q<A, B>, Not<Not<Q<A, B>>>> {
    unimplemented!()
}

/// Converts to equality `(a ~~ b) => (a == b)`.
pub fn to_eq<A: Prop, B: Prop>((eq, _): Q<A, B>) -> Eq<A, B> {
    eq
}

/// Converts to equality `(a ~¬~ b) => (a == b)`.
pub fn aq_to_eq<A: Prop, B: Prop>((eq, _): Aq<A, B>) -> Eq<A, B> {
    eq
}

/// Converts to equality of self-quality `(a ~~ b) => ((a ~~ a) == (b ~~ b))`.
pub fn to_eq_q<A: Prop, B: Prop>(q: Q<A, B>) -> Eq<Q<A, A>, Q<B, B>> {
    (right(q.clone()).map_any(), left(q).map_any())
}

/// Converts to equality of self-quality `(a ~¬~ b) => ((a ~¬~ a) == (b ~¬~ b))`.
pub fn to_eq_aq<A: Prop, B: Prop>(q: Aq<A, B>) -> Eq<Aq<A, A>, Aq<B, B>> {
    (aq_right(q.clone()).map_any(), aq_left(q).map_any())
}

/// `(a ~~ b) => (a ~~ a)`.
pub fn left<A: Prop, B: Prop>(q_ab: Q<A, B>) -> Q<A, A> {
    let q_ba = symmetry(q_ab.clone());
    transitivity(q_ab, q_ba)
}

/// `(a ~¬~ b) => (a ~¬~ a)`.
pub fn aq_left<A: Prop, B: Prop>(q_ab: Aq<A, B>) -> Aq<A, A> {
    let q_ba = aq_symmetry(q_ab.clone());
    aq_transitivity(q_ab, q_ba)
}

/// `(a ~~ b) => (b ~~ b)`.
pub fn right<A: Prop, B: Prop>(q_ab: Q<A, B>) -> Q<B, B> {
    let q_ba = symmetry(q_ab.clone());
    transitivity(q_ba, q_ab)
}

/// `(a ~¬~ b) => (b ~¬~ b)`.
pub fn aq_right<A: Prop, B: Prop>(q_ab: Aq<A, B>) -> Aq<B, B> {
    let q_ba = aq_symmetry(q_ab.clone());
    aq_transitivity(q_ba, q_ab)
}

/// Introduce a different proposition in right argument (keep left).
pub fn sesh_left<A: Prop, B: Prop>(sesh_a: Not<Q<A, A>>) -> Not<Q<A, B>> {
    Rc::new(move |q_ab| sesh_a(left(q_ab)))
}

/// Introduce a different proposition in right argument (keep left).
pub fn aq_sesh_left<A: Prop, B: Prop>(sesh_a: Not<Aq<A, A>>) -> Not<Aq<A, B>> {
    Rc::new(move |q_ab| sesh_a(aq_left(q_ab)))
}

/// Introduce a different proposition in left argument (keep right).
pub fn sesh_right<A: Prop, B: Prop>(sesh_b: Not<Q<B, B>>) -> Not<Q<A, B>> {
    Rc::new(move |q_ab| sesh_b(right(q_ab)))
}

/// Introduce a different proposition in left argument (keep right).
pub fn aq_sesh_right<A: Prop, B: Prop>(sesh_b: Not<Aq<B, B>>) -> Not<Aq<A, B>> {
    Rc::new(move |q_ab| sesh_b(aq_right(q_ab)))
}

/// `¬(a == b) => ¬(a ~~ b)`.
pub fn neq_to_sesh<A: Prop, B: Prop>(neq: Not<Eq<A, B>>) -> Not<Q<A, B>> {
    Rc::new(move |q_ab| neq(to_eq(q_ab)))
}

/// `¬(a == b) => ¬(a ~~ b)`.
pub fn neq_to_aq_sesh<A: Prop, B: Prop>(neq: Not<Eq<A, B>>) -> Not<Aq<A, B>> {
    Rc::new(move |q_ab| neq(aq_to_eq(q_ab)))
}

/// Convert inquality to inequality `¬(a ~~ b) ⋀ eqq(a, b) => ¬(a == b)`.
pub fn sesh_to_neq<A: Prop, B: Prop>(sesh: Not<Q<A, B>>, eqq_ab: EqQ<A, B>) -> Not<Eq<A, B>> {
    imply::modus_tollens(eqq_ab)(sesh)
}

/// Convert inquality to inequality `¬(a ~¬~ b) ⋀ eqaq(a, b) => ¬(a == b)`.
pub fn aq_sesh_to_neq<A: Prop, B: Prop>(sesh: Not<Aq<A, B>>, eqq_ab: EqAq<A, B>) -> Not<Eq<A, B>> {
    imply::modus_tollens(eqq_ab)(sesh)
}

/// `eqq(a, b)  =>  ¬(a ~~ b) == ¬(a == b)`.
pub fn sesh_eq_neq<A: Prop, B: Prop>(eqq_ab: EqQ<A, B>) -> Eq<Not<Q<A, B>>, Not<Eq<A, B>>> {
    (
        Rc::new(move |nq_ab| sesh_to_neq(nq_ab, eqq_ab.clone())),
        Rc::new(move |neq_ab| neq_to_sesh(neq_ab)),
    )
}

/// `eqaq(a, b)  =>  ¬(a ~¬~ b) == ¬(a == b)`.
pub fn aq_sesh_eq_neq<A: Prop, B: Prop>(eqq_ab: EqAq<A, B>) -> Eq<Not<Aq<A, B>>, Not<Eq<A, B>>> {
    (
        Rc::new(move |nq_ab| aq_sesh_to_neq(nq_ab, eqq_ab.clone())),
        Rc::new(move |neq_ab| neq_to_aq_sesh(neq_ab)),
    )
}

/// Mirror with pure Platonism
/// `((a == a) => ( (a ~~ a) ⋁ ¬¬(a ~~ a) )) => ¬¬(a ~~ a)`.
pub fn mirror_plato<A: Prop>(plato_a: PurePlatonism<A, A>) -> Not<Not<Q<A, A>>> {
    match plato_a(eq::refl()) {
        Left(q_aa) => not::double(q_aa),
        Right(nn_q_aa) => nn_q_aa,
    }
}

/// Mirror `¬¬(a ~~ a)`.
#[cfg(feature = "pure_platonism")]
pub fn mirror<A: Prop>() -> Not<Not<Q<A, A>>> {
    match eq_lift(eq::refl()) {
        Left(q_aa) => not::double(q_aa),
        Right(nn_q_aa) => nn_q_aa,
    }
}

/// Excluded middle with pure Platonism implies reflexivity.
pub fn excm_plato_refl<A: Prop>(exc: ExcM<Q<A, A>>, plato_a: PurePlatonism<A, A>) -> Q<A, A> {
    match exc {
        Left(q) => q,
        Right(n_q) => imply::absurd()(mirror_plato(plato_a)(n_q)),
    }
}

/// Excluded middle implies reflexivity.
#[cfg(feature = "pure_platonism")]
pub fn excm_refl<A: Prop>(exc: ExcM<Q<A, A>>) -> Q<A, A> {
    match exc {
        Left(q) => q,
        Right(n_q) => imply::absurd()(mirror()(n_q)),
    }
}

/// `¬(a ~~ b) ⋀ (a == b) ⋀ ((a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )) => c`.
pub fn absurd_plato<A: Prop, B: Prop, C: Prop>(
    n_q: Not<Q<A, B>>,
    eq: Eq<A, B>,
    plato_ab: PurePlatonism<A, B>,
) -> C {
    match plato_ab(eq) {
        Left(q) => not::absurd(n_q, q),
        Right(nn_q) => not::absurd(nn_q, n_q),
    }
}

/// `¬(a ~~ b) ⋀ (a == b) => c`.
#[cfg(feature = "pure_platonism")]
pub fn absurd<A: Prop, B: Prop, C: Prop>(
    n_q: Not<Q<A, B>>,
    eq: Eq<A, B>,
) -> C {
    match eq_lift(eq) {
        Left(q) => not::absurd(n_q, q),
        Right(nn_q) => not::absurd(nn_q, n_q),
    }
}

/// `¬(a ~~ a) ⋀ ((a == a) => ( (a ~~ a) ⋁ ¬¬(a ~~ a) )) => b`.
pub fn sesh_plato_absurd<A: Prop, B: Prop>(
    f: Not<Q<A, A>>,
    plato_a: PurePlatonism<A, A>,
) -> B {
    not::absurd(mirror_plato(plato_a), f)
}

/// `¬(a ~~ a) => b`.
#[cfg(feature = "pure_platonism")]
pub fn sesh_absurd<A: Prop, B: Prop>(f: Not<Q<A, A>>) -> B {
    not::absurd(mirror(), f)
}

/// `(a ~~ b) ∧ (a == c)  =>  (c ~~ b)`.
#[cfg(feature = "subst_equality")]
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(_: Q<A, B>, _: Eq<A, C>) -> Q<C, B> {
    unimplemented!()
}

/// `(a ~¬~ b) ∧ (a == c)  =>  (c ~¬~ b)`.
#[cfg(feature = "subst_equality")]
pub fn aq_in_left_arg<A: Prop, B: Prop, C: Prop>(_: Aq<A, B>, _: Eq<A, C>) -> Aq<C, B> {
    unimplemented!()
}

/// `(a ~~ b) ∧ (b == c)  =>  (a ~~ c)`.
#[cfg(feature = "subst_equality")]
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(_: Q<A, B>, _: Eq<B, C>) -> Q<A, C> {
    unimplemented!()
}

/// `(a ~¬~ b) ∧ (b == c)  =>  (a ~¬~ c)`.
#[cfg(feature = "subst_equality")]
pub fn aq_in_right_arg<A: Prop, B: Prop, C: Prop>(_: Aq<A, B>, _: Eq<B, C>) -> Aq<A, C> {
    unimplemented!()
}

/// `(a ~~ b) ∧ hom_eq(2, a, c)  =>  (c ~~ b)`.
pub fn hom_in_left_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qa, qb)): Q<A, B>,
    (eq_q, (eq_ac, True)): HomEq2<A, C>
) -> Q<C, B> {
    let eq2: Eq<C, B> = eq::transitivity(eq::symmetry(qubit::to_eq(eq_ac)), eq_ab);
    let qc: Qu<C> = eq_q.0(qa);
    (eq2, (qc, qb))
}

/// `(a ~¬~ b) ∧ hom_eq(2, a, c)  =>  (c ~¬~ b)`.
pub fn aq_hom_in_left_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qa, qb)): Aq<A, B>,
    (eq_q, (eq_ac, True)): HomEq2<A, C>
) -> Aq<C, B> {
    let eq2: Eq<C, B> = eq::transitivity(eq::symmetry(qubit::to_eq(eq_ac)), eq_ab);
    let qc: Qu<Not<C>> = qubit::eq_to_eq_inv(eq_q).0(qa);
    (eq2, (qc, qb))
}

/// `(a ~~ b) ∧ hom_eq(2, b, c)  =>  (a ~~ c)`.
pub fn hom_in_right_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qa, qb)): Q<A, B>,
    (eq_q, (eq_bc, True)): HomEq2<B, C>
) -> Q<A, C> {
    let eq2: Eq<A, C> = eq::transitivity(eq_ab, qubit::to_eq(eq_bc));
    let qc: Qu<C> = eq_q.0(qb);
    (eq2, (qa, qc))
}

/// `(a ~¬~ b) ∧ hom_eq(2, b, c)  =>  (a ~¬~ c)`.
pub fn aq_hom_in_right_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qa, qb)): Aq<A, B>,
    (eq_q, (eq_bc, True)): HomEq2<B, C>
) -> Aq<A, C> {
    let eq2: Eq<A, C> = eq::transitivity(eq_ab, qubit::to_eq(eq_bc));
    let qc: Qu<Not<C>> = qubit::eq_to_eq_inv(eq_q).0(qb);
    (eq2, (qa, qc))
}

/// `¬(a ~~ b) ⋀ (a == c)  =>  ¬(c ~~ b)`.
#[cfg(feature = "subst_equality")]
pub fn sesh_in_left_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Q<A, B>>,
    eq_ac: Eq<A, C>,
) -> Not<Q<C, B>> {
    let eq_ca = eq::symmetry(eq_ac);
    Rc::new(move |q_cb| {
        sesh_ab(in_left_arg(q_cb, eq_ca.clone()))
    })
}

/// `¬(a ~¬~ b) ⋀ (a == c)  =>  ¬(c ~¬~ b)`.
#[cfg(feature = "subst_equality")]
pub fn aq_sesh_in_left_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Aq<A, B>>,
    eq_ac: Eq<A, C>,
) -> Not<Aq<C, B>> {
    let eq_ca = eq::symmetry(eq_ac);
    Rc::new(move |q_cb| {
        sesh_ab(aq_in_left_arg(q_cb, eq_ca.clone()))
    })
}

/// `¬(a ~~ b) ⋀ (b == c)  =>  ¬(a ~~ c)`.
#[cfg(feature = "subst_equality")]
pub fn sesh_in_right_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Q<A, B>>,
    eq_bc: Eq<B, C>,
) -> Not<Q<A, C>> {
    let eq_cb = eq::symmetry(eq_bc);
    Rc::new(move |q_ac| {
        sesh_ab(in_right_arg(q_ac, eq_cb.clone()))
    })
}

/// `¬(a ~¬~ b) ⋀ (b == c)  =>  ¬(a ~¬~ c)`.
#[cfg(feature = "subst_equality")]
pub fn aq_sesh_in_right_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Aq<A, B>>,
    eq_bc: Eq<B, C>,
) -> Not<Aq<A, C>> {
    let eq_cb = eq::symmetry(eq_bc);
    Rc::new(move |q_ac| {
        sesh_ab(aq_in_right_arg(q_ac, eq_cb.clone()))
    })
}

/// `¬(a ~~ b) ⋀ hom_eq(2, a, c)  =>  ¬(c ~~ b)`.
pub fn sesh_hom_in_left_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Q<A, B>>,
    eq_ac: HomEq2<A, C>,
) -> Not<Q<C, B>> {
    let eq_ca = univalence::hom_eq_symmetry::<nat::Two, _, _>(eq_ac);
    Rc::new(move |q_cb| {
        sesh_ab(hom_in_left_arg(q_cb, eq_ca.clone()))
    })
}

/// `¬(a ~¬~ b) ⋀ hom_eq(2, a, c)  =>  ¬(c ~¬~ b)`.
pub fn aq_sesh_hom_in_left_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Aq<A, B>>,
    eq_ac: HomEq2<A, C>,
) -> Not<Aq<C, B>> {
    let eq_ca = univalence::hom_eq_symmetry::<nat::Two, _, _>(eq_ac);
    Rc::new(move |q_cb| {
        sesh_ab(aq_hom_in_left_arg(q_cb, eq_ca.clone()))
    })
}

/// `¬(a ~~ b) ⋀ (b == c)  =>  ¬(a ~~ c)`.
pub fn sesh_hom_in_right_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Q<A, B>>,
    eq_bc: HomEq2<B, C>,
) -> Not<Q<A, C>> {
    let eq_cb = univalence::hom_eq_symmetry::<nat::Two, _, _>(eq_bc);
    Rc::new(move |q_ac| {
        sesh_ab(hom_in_right_arg(q_ac, eq_cb.clone()))
    })
}

/// `¬(a ~¬~ b) ⋀ (b == c)  =>  ¬(a ~¬~ c)`.
pub fn aq_sesh_hom_in_right_arg<A: Prop, B: Prop, C: Prop>(
    sesh_ab: Not<Aq<A, B>>,
    eq_bc: HomEq2<B, C>,
) -> Not<Aq<A, C>> {
    let eq_cb = univalence::hom_eq_symmetry::<nat::Two, _, _>(eq_bc);
    Rc::new(move |q_ac| {
        sesh_ab(aq_hom_in_right_arg(q_ac, eq_cb.clone()))
    })
}

/// `¬(a ~~ a) => (¬a ~~ ¬a)`.
pub fn sesh_to_q_inv<A: Prop>(f: Not<Q<A, A>>) -> Q<Not<A>, Not<A>> {
    let sesh: Not<Qu<A>> = Rc::new(move |x| f((eq::refl(), (x.clone(), x))));
    let qu: Qu<Not<A>> = qubit::sesh_to_inv(sesh);
    (eq::refl(), (qu.clone(), qu))
}

/// `¬(a ~¬~ a) => (¬a ~¬~ ¬a)`.
pub fn aq_sesh_to_q_inv<A: Prop>(f: Not<Aq<A, A>>) -> Aq<Not<A>, Not<A>> {
    let sesh: Not<Qu<Not<A>>> = Rc::new(move |x| f((eq::refl(), (x.clone(), x))));
    let qu: Qu<Not<Not<A>>> = qubit::sesh_to_inv(sesh);
    (eq::refl(), (qu.clone(), qu))
}

/// `(¬a ~~ ¬a) => ¬(a ~~ a)`.
pub fn q_inv_to_sesh<A: Prop>((_, (nqu, _)): Q<Not<A>, Not<A>>) -> Not<Q<A, A>> {
    Rc::new(move |q| {
        qubit::inv_to_sesh(nqu.clone())(Qu::from_q(q))
    })
}

/// `(¬a ~¬~ ¬a) => ¬(a ~¬~ a)`.
pub fn aq_inv_to_sesh<A: Prop>((_, (nqu, _)): Aq<Not<A>, Not<A>>) -> Not<Aq<A, A>> {
    Rc::new(move |q| {
        qubit::inv_to_sesh(nqu.clone())(Qu::from_aq(q))
    })
}
