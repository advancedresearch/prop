//! Path Semantical Quality
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
//! Interpreted as an [Avatar Graph](https://advancedresearch.github.io/avatar-extensions/summary.html#avatar-graphs),
//! the core is `a == b` and there are two 1-avatars:
//!
//! - `(a ~~ b)`
//! - `¬¬(a ~~ b)`
//!
//! The 2-avatar integrates `(a ~~ b)` and `¬¬(a ~~ b)` using `⋁`.

use crate::*;

/// Quality between `A` and `B` (`A ~~ B`).
#[derive(Clone)]
pub struct Q<A, B>(Eq<A, B>);

/// Symmetry `(a ~~ b) => (b ~~ a)`.
pub fn symmetry<A: Prop, B: Prop>(Q((ab, ba)): Q<A, B>) -> Q<B, A> {
    Q((ba, ab))
}

/// Transitivity `(a ~~ b) ⋀ (b ~~ c) => (a ~~ c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    Q((ab, ba)): Q<A, B>,
    Q((bc, cb)): Q<B, C>
) -> Q<A, C> {
    Q((Rc::new(move |a| bc(ab(a))), Rc::new(move |c| ba(cb(c)))))
}

/// Equality lift `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
pub fn eq_lift<A: Prop, B: Prop>(eq: Eq<A, B>) -> Or<Q<A, B>, Not<Not<Q<A, B>>>> {
    Left(Q(eq))
}

/// Converts to equality `(a ~~ b) => (a == b)`.
pub fn to_eq<A: Prop, B: Prop>(Q(eq): Q<A, B>) -> Eq<A, B> {
    eq
}

/// `(a ~~ b) => (a ~~ a)`.
pub fn self_quality_left<A: Prop, B: Prop>(q_ab: Q<A, B>) -> Q<A, A> {
    let q_ba = symmetry(q_ab.clone());
    transitivity(q_ab, q_ba)
}

/// `(a ~~ b) => (b ~~ b)`.
pub fn self_quality_right<A: Prop, B: Prop>(q_ab: Q<A, B>) -> Q<B, B> {
    let q_ba = symmetry(q_ab.clone());
    transitivity(q_ba, q_ab)
}

/// `¬(a ~~ a) => ¬(a ~~ b)`.
pub fn sesh_left<A: Prop, B: Prop>(sesh_a: Not<Q<A, A>>) -> Not<Q<A, B>> {
    Rc::new(move |not_q_ab| sesh_a(self_quality_left(not_q_ab)))
}

/// `¬(b ~~ b) => ¬(a ~~ b)`.
pub fn sesh_right<A: Prop, B: Prop>(sesh_b: Not<Q<B, B>>) -> Not<Q<A, B>> {
    Rc::new(move |not_q_ab| sesh_b(self_quality_right(not_q_ab)))
}

/// Mirror `¬¬(a ~~ a)`.
pub fn mirror<A: Prop>() -> Not<Not<Q<A, A>>> {
    match eq_lift(eq::refl()) {
        Left(q_aa) => not::double(q_aa),
        Right(nn_q_aa) => nn_q_aa,
    }
}

/// Excluded middle implies reflexivity.
pub fn excm_refl<A: Prop>(exc: ExcM<Q<A, A>>) -> Q<A, A> {
    match exc {
        Left(q) => q,
        Right(n_q) => imply::absurd()(mirror()(n_q)),
    }
}
