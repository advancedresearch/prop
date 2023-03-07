//! # Path Semantical Quality
//!
//! Path Semantical Quality is a partial equivalence relation that lifts biconditions
//! with symbolic distinction.
//! See [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/path-semantical-quality.pdf).
//!
//! If this is your first time, then you might want to check out the [path_semantics] module first.
//!
//! For a different implementation of quality, see [PSI in Avalog](https://github.com/advancedresearch/avalog/blob/master/source/psi.txt).
//!
//! There is also an implementation in [Pocket-Prover](https://github.com/advancedresearch/pocket_prover).
//!
//! Path semantical quality is written `~~`, e.g. `a ~~ b` (see [Q]).
//!
//! ### Work-around for symbolic distinction
//!
//! IPL does not support symbolic distinction, so quality must be assumed explicitly.
//!
//! There are some ways to cheat though, e.g. using [hooo::lift_q] or [fun::inv::self_inv_to_q].
//!
//! For more information about symbolic distinction, see the [path_semantics] module.
//!
//! ### Lifting equality into quality
//!
//! `EqQ<A, B>` (see [EqQ])
//!
//! Although IPL does not support symbolic distinction,
//! one can use `EqQ<A, B>` (`(a == b) => (a ~~ b)`) to model symbolic distinction.
//! This means `EqQ<A, B>` can be used as an assumption that `A` and `B` are symbolic distinct.
//!
//! ### Seshatism vs Platonism
//!
//! In philosophy of mathematics, path semantical quality can be used to talk about the distinction
//! between bias of Seshatic (dual-Platonic) languages and Platonic langauges.
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
//! For more information, see [Seshatism vs Platonism](https://advancedresearch.github.io/avatar-extensions/summary.html#seshatism-vs-platonism).
//!
//! ### Seshatic Relations
//!
//! `Seshatic<A, B>` (see [Seshatic])
//!
//! When a relation `p(a, b)` is Seshatic,
//! it means that it implies Seshatism of either `a` or `b`:
//!
//! `p(a, b) => ¬(a ~~ a) ⋁ ¬(b ~~ b)`
//!
//! ### Aquality
//!
//! Aquality is a Seshatic relation that is symmetric to quality ([Aq]).
//! It means, when substituting quality with aquality and vice versa,
//! one can prove the same theorems.
//!
//! One can think about aquality vs quality as a perspective
//! where Seshatism and Platonism become mirror images of each other.
//!
//! The core axiom biases mathematics toward Platonism,
//! but this choice is arbitrary since `¬~x == ~¬x` (see [qubit::eq_sesh_inv]).
//! Therefore, "Platonism" is whatever theory/philosophy
//! that is associated with the quality/aquality used in a core axiom.
//! The dual theory/philosophy is Seshatism.
//!
//! Dualities of this form are common in mathematics,
//! so Seshatism vs Platonism is often used to talk about analogues of other dualities as well.

use crate::*;

use univalence::HomEq2;
use qubit::Qu;
use hooo::Theory;

/// Lifts equality into quality `(a == b) => (a ~~ b)`.
pub type EqQ<A, B> = Imply<Eq<A, B>, Q<A, B>>;
/// Lifts equality into aquality.
pub type EqAq<A, B> = Imply<Eq<A, B>, Aq<A, B>>;
/// A Seshatic relation `¬(a ~~ a) ⋁ ¬(b ~~ b)`.
pub type Seshatic<A, B> = Or<Not<Q<A, A>>, Not<Q<B, B>>>;

/// Quality definition `(a ~~ b) == ((a == b) ⋀ ~a ⋀ ~b)`.
pub type Q<A, B> = And<Eq<A, B>, And<Qu<A>, Qu<B>>>;

/// Aquality definition `(a ~¬~ b) == ((a == b) ⋀ ~¬a ⋀ ~¬b)`.
pub type Aq<A, B> = And<Eq<A, B>, And<Qu<Not<A>>, Qu<Not<B>>>>;

/// Symmetry `(a ~~ b) => (b ~~ a)`.
pub fn symmetry<A: Prop, B: Prop>((eq, and_qu): Q<A, B>) -> Q<B, A> {
    (eq::symmetry(eq), and::symmetry(and_qu))
}

/// `(a ~~ b) == (b ~~ a)`.
pub fn eq_q_symmetry<A: Prop, B: Prop>() -> Eq<Q<A, B>, Q<B, A>> {
    (Rc::new(symmetry), Rc::new(symmetry))
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
    Rc::new(move |q| qubit::inv_to_sesh(nqu.clone())(Qu::from_q(q)))
}

/// `(¬a ~¬~ ¬a) => ¬(a ~¬~ a)`.
pub fn aq_inv_to_sesh<A: Prop>((_, (nqu, _)): Aq<Not<A>, Not<A>>) -> Not<Aq<A, A>> {
    Rc::new(move |q| qubit::inv_to_sesh(nqu.clone())(Qu::from_aq(q)))
}

/// `theory(a == b) => eqq(a, b)`.
pub fn theory_eq_to_eqq<A: Prop, B: Prop>(theory: Theory<Eq<A, B>>) -> EqQ<A, B> {
    Rc::new(move |eq| hooo::lift_q(eq, theory.clone()))
}

/// `eqq(a, b) => ((a ~~ b) ⋁ ¬(a ~~ b))`.
pub fn eqq_to_excm_q<A: DProp, B: DProp>(eqq: EqQ<A, B>) -> ExcM<Q<A, B>> {
    eqq_to_excm_q_with_excm_eq(eqq, Eq::<A, B>::decide())
}

/// `eqq(a, b) ⋀ ((a == b) ⋁ ¬(a == b))  =>  ((a ~~ b) ⋁ ¬(a ~~ b))`.
pub fn eqq_to_excm_q_with_excm_eq<A: Prop, B: Prop>(
    eqq: EqQ<A, B>,
    excm_eq: ExcM<Eq<A, B>>
) -> ExcM<Q<A, B>> {
    match excm_eq {
        Left(eq) => Left(eqq(eq)),
        Right(neq) => Right(imply::in_left(neq, |x| to_eq(x))),
    }
}

/// `theory(a == b) ⋀ ((a == b) ⋁ ¬(a == b))  =>  ((a ~~ b) ⋁ ¬(a ~~ b))`.
///
/// There is no analogue `theory_eq_to_excm_q` for decidable propositions,
/// because `theory(a == b) ⋀ ((a == b) ⋁ ¬(a == b))^true` is absurd.
pub fn theory_eq_to_excm_q_with_excm_eq<A: Prop, B: Prop>(
    theory_eq: Theory<Eq<A, B>>,
    excm_eq: ExcM<Eq<A, B>>
) -> ExcM<Q<A, B>> {
    eqq_to_excm_q_with_excm_eq(theory_eq_to_eqq(theory_eq), excm_eq)
}
