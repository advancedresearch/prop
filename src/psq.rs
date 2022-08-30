//! # PSQ - Path Semantical Quantum Propositional Logic
//!
//! Allows writing generic code over various PSQ-logics,
//! without assuming a set of axioms of the underlying qubit operator.

use crate::*;

pub use q_commute as q_symmetry;
pub use aq_commute as aq_symmetry;
pub use nq_commute as nq_symmetry;
pub use naq_commute as naq_symmetry;

/// Qubit type.
pub type Qubit<Psq, A> = <Psq as PSQ>::Qubit<A>;

/// Quality type.
pub type Qual<Psq, A, B> = And<Eq<A, B>, And<Qubit<Psq, A>, Qubit<Psq, B>>>;

/// Aquality type.
pub type Aqual<Psq, A, B> = And<Eq<A, B>, And<Qubit<Psq, Not<A>>, Qubit<Psq, Not<B>>>>;

/// Implemented by different kinds of path semantical quality.
pub trait PSQ {
    /// Qubit operator.
    type Qubit<A>;
}

/// Symmetry `(a ~~ b) => (b ~~ a)`.
pub fn q_commute<Psq: PSQ, A: Prop, B: Prop>(q: Qual<Psq, A, B>) -> Qual<Psq, B, A> {
    (eq::commute(q.0), (q.1.1, q.1.0))
}

/// Symmetry `(a ~¬~ b) => (b ~¬~ a)`.
pub fn aq_commute<Psq: PSQ, A: Prop, B: Prop>(aq: Aqual<Psq, A, B>) -> Aqual<Psq, B, A> {
    (eq::commute(aq.0), (aq.1.1, aq.1.0))
}

/// Negated symmetry `¬(a ~~ b) => ¬(b ~~ a)`.
pub fn nq_commute<Psq: PSQ, A: Prop, B: Prop>(nq: Not<Qual<Psq, A, B>>) -> Not<Qual<Psq, B, A>>
    where Psq::Qubit<A>: 'static,
          Psq::Qubit<B>: 'static,
{
    Rc::new(move |q| nq(q_commute::<Psq, B, A>(q)))
}

/// Negated symmetry `¬(a ~¬~ b) => ¬(b ~¬~ a)`.
pub fn naq_commute<Psq: PSQ, A: Prop, B: Prop>(nq: Not<Aqual<Psq, A, B>>) -> Not<Aqual<Psq, B, A>>
    where Psq::Qubit<Not<A>>: 'static,
          Psq::Qubit<Not<B>>: 'static,
{
    Rc::new(move |q| nq(aq_commute::<Psq, B, A>(q)))
}

/// Transitivity `(a ~~ b) ⋀ (b ~~ c) => (a ~~ c)`.
pub fn q_transitivity<Psq: PSQ, A: Prop, B: Prop, C: Prop>(
    f: Qual<Psq, A, B>,
    g: Qual<Psq, B, C>
) -> Qual<Psq, A, C> {
    (eq::transitivity(f.0, g.0), (f.1.0, g.1.1))
}

/// Transitivity `(a ~¬~ b) ⋀ (b ~¬~ c) => (a ~¬~ c)`.
pub fn aq_transitivity<Psq: PSQ, A: Prop, B: Prop, C: Prop>(
    f: Aqual<Psq, A, B>,
    g: Aqual<Psq, B, C>
) -> Aqual<Psq, A, C> {
    (eq::transitivity(f.0, g.0), (f.1.0, g.1.1))
}

/// `~a => (a ~~ a)`.
pub fn qu_to_q<Psq: PSQ, A: Prop>(x: Qubit<Psq, A>) -> Qual<Psq, A, A>
    where Qubit<Psq, A>: Clone
{
    (eq::refl(), (x.clone(), x))
}

/// `~¬a => (a ~¬~ a)`.
pub fn qun_to_aq<Psq: PSQ, A: Prop>(x: Qubit<Psq, Not<A>>) -> Aqual<Psq, A, A>
    where Qubit<Psq, Not<A>>: Clone
{
    (eq::refl(), (x.clone(), x))
}

/// `(a ~~ a) => ~a`.
pub fn q_to_qu<Psq: PSQ, A: Prop>(f: Qual<Psq, A, A>) -> Qubit<Psq, A> {
    f.1.0
}

/// `(a ~¬~ a) => ~¬a`.
pub fn aq_to_qun<Psq: PSQ, A: Prop>(f: Aqual<Psq, A, A>) -> Qubit<Psq, Not<A>> {
    f.1.0
}

/// `(a ~~ b) => (a == b)`.
pub fn q_to_eq<Psq: PSQ, A: Prop, B: Prop>(f: Qual<Psq, A, B>) -> Eq<A, B> {
    f.0
}

/// `(a ~¬~ b) => (a == b)`.
pub fn aq_to_eq<Psq: PSQ, A: Prop, B: Prop>(f: Aqual<Psq, A, B>) -> Eq<A, B> {
    f.0
}

/// `(a ~~ b) => (a ~~ a)`.
pub fn q_left<Psq: PSQ, A: Prop, B: Prop>(f: Qual<Psq, A, B>) -> Qual<Psq, A, A>
    where Qual<Psq, A, B>: Clone
{
    q_transitivity::<Psq, A, B, A>(f.clone(), q_commute::<Psq, A, B>(f))
}

/// `(a ~¬~ b) => (a ~¬~ a)`.
pub fn aq_left<Psq: PSQ, A: Prop, B: Prop>(f: Aqual<Psq, A, B>) -> Aqual<Psq, A, A>
    where Aqual<Psq, A, B>: Clone
{
    aq_transitivity::<Psq, A, B, A>(f.clone(), aq_commute::<Psq, A, B>(f))
}

/// `(a ~~ b) => (b ~~ b)`.
pub fn q_right<Psq: PSQ, A: Prop, B: Prop>(f: Qual<Psq, A, B>) -> Qual<Psq, B, B>
    where Qual<Psq, A, B>: Clone
{
    q_transitivity::<Psq, B, A, B>(q_commute::<Psq, A, B>(f.clone()), f)
}

/// `(a ~¬~ b) => (b ~¬~ b)`.
pub fn aq_right<Psq: PSQ, A: Prop, B: Prop>(f: Aqual<Psq, A, B>) -> Aqual<Psq, B, B>
    where Aqual<Psq, A, B>: Clone
{
    aq_transitivity::<Psq, B, A, B>(aq_commute::<Psq, A, B>(f.clone()), f)
}
