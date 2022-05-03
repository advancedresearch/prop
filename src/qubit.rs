//! # Path Semantical Qubit
//!
//! For an implementation, see the [Pocket-Prover](https://github.com/advancedresearch/pocket_prover) library.

use crate::*;
use nat::{Z, S};
use quality::Q;

/// Represents a recursive qubit proposition.
#[derive(Clone)]
pub struct Qubit<N, A>(N, A);

impl<A: Prop> Qubit<Z, A> {
    /// Get proposition.
    pub fn to(self) -> A {self.1}
    /// From proposition.
    pub fn from(a: A) -> Self {Qubit(Z, a)}
}

impl<A: Prop> Qubit<S<Z>, A> {
    /// Convert to self-quality.
    pub fn to_q(self) -> Q<A, A> {Q((self.1.clone().map_any(), self.1.map_any()))}
    /// Convert from self-quality.
    pub fn from_q(_: Q<A, A>) -> Self {unimplemented!()}
}

/// Convert to equality.
pub fn to_eq<A: Prop, B: Prop>(x: Eq<Qubit<Z, A>, Qubit<Z, B>>) -> Eq<A, B> {
    let x2 = x.clone();
    (
        Rc::new(move |a| x2.0(Qubit::from(a)).to()),
        Rc::new(move |b| x.1(Qubit::from(b)).to()),
    )
}

/// Convert to equality.
pub fn to_eq_q<A: Prop, B: Prop>(x: Eq<Qubit<S<Z>, A>, Qubit<S<Z>, B>>) -> Eq<Q<A, A>, Q<B, B>> {
    let x2 = x.clone();
    (
        Rc::new(move |qa| x2.0(Qubit::from_q(qa)).to_q()),
        Rc::new(move |qb| x.1(Qubit::from_q(qb)).to_q())
    )
}
