//! # Path Semantical Quality
//!
//! See [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/path-semantical-quality.pdf).
//!
//! For a different implementation of quality, see [PSI in Avalog](https://github.com/advancedresearch/avalog/blob/master/source/psi.txt).
//!
//! ### Seshatism
//!
//! [Seshatism](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatism.pdf)
//! is a way to reject two forms of Platonism:
//!
//! - `¬(a ~~ a)`: Seshatism (Moment Witness)
//! - `a ~~ a`: Platonism 1 (Loop Witness)
//! - `a ~~ b`: Platonism 2 (Product Witness)
//!
//! Since `a ~~ b` implies `a ~~ a`, both Loop and Product Witness are rejected.
//!
//! Seshatism forces the logical structure around the proposition to be a [DAG](https://en.wikipedia.org/wiki/Directed_acyclic_graph)
//! (Directed Acyclic Graph).
//!
//! ### Work-arounds for symbolic distinction
//!
//! IPL does not support symbolic distinction,
//! so there are two supported work-arounds that are safe to use:
//!
//! - Add argument to explicitly assume lifting equality into quality
//! - Add argument or assume pure Platonism using "pure_platonism" feature flag
//!
//! ### Lifting equality into quality
//!
//! `EqQ<A, B>`
//!
//! This implementation lifts equality directly to quality.
//! Since this is unsound without symbolic distinction,
//! it is not possible to assume this directly.
//!
//! If you want to prove stuff about Seshatism,
//! this is the only way.
//!
//! ### Pure Platonism
//!
//! `PurePlatonism<A, B>`
//!
//! Feature flag: "pure_platonism"
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

use crate::*;

pub use commute as symmetry;

/// Lifts equality into quality.
pub type EqQ<A, B> = Imply<Eq<A, B>, Q<A, B>>;
/// Pure Platonism assumption.
pub type PurePlatonism<A, B> = Imply<Eq<A, B>, Or<Q<A, B>, Not<Not<Q<A, B>>>>>;

/// Quality between `A` and `B` (`A ~~ B`).
#[derive(Clone)]
pub struct Q<A, B>(Eq<A, B>);

/// Symmetry `(a ~~ b) => (b ~~ a)`.
pub fn commute<A: Prop, B: Prop>(Q((ab, ba)): Q<A, B>) -> Q<B, A> {
    Q((ba, ab))
}

/// Transitivity `(a ~~ b) ⋀ (b ~~ c) => (a ~~ c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    Q((ab, ba)): Q<A, B>,
    Q((bc, cb)): Q<B, C>
) -> Q<A, C> {
    Q((Rc::new(move |a| bc(ab(a))), Rc::new(move |c| ba(cb(c)))))
}

/// Equality maybe lift `(a == b) => ( (a ~~ b) ⋁ true )`.
pub fn eq_maybe_lift<A: Prop, B: Prop>(eq: Eq<A, B>) -> Or<Q<A, B>, True> {
    Left(Q(eq))
}

/// Equality lift `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
#[cfg(feature = "pure_platonism")]
pub fn assume_pure_platonism<A: Prop, B: Prop>() -> PurePlatonism<A, B> {
    Rc::new(move |eq| Left(Q(eq)))
}

/// Equality lift `(a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) )`.
#[cfg(feature = "pure_platonism")]
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

/// Introduce a different proposition in right argument (keep left).
pub fn sesh_left<A: Prop, B: Prop>(sesh_a: Not<Q<A, A>>) -> Not<Q<A, B>> {
    Rc::new(move |q_ab| sesh_a(self_quality_left(q_ab)))
}

/// Introduce a different proposition in left argument (keep right).
pub fn sesh_right<A: Prop, B: Prop>(sesh_b: Not<Q<B, B>>) -> Not<Q<A, B>> {
    Rc::new(move |q_ab| sesh_b(self_quality_right(q_ab)))
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
