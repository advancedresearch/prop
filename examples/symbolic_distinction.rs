#[cfg(feature = "quantify")]
use prop::*;
#[cfg(feature = "quantify")]
use prop::univalence::{Univ};
#[cfg(feature = "quantify")]
use prop::quantify::{App2, Pred};
#[cfg(feature = "quantify")]
use prop::quality::{EqQ, Q};
#[cfg(feature = "quantify")]
use std::rc::Rc;

/// This example shows that symbolic distinction is equal to univalence.
///
/// This is done by modeling symbolic distiction as a predicate:
///
/// 1. Define the predicate as symbolic distinction using `quality::EqQ`.
/// 2. Prove that the predicate equals univalence using `univalence::Univ`.
///
/// Since the predicate is modeled by both symbolic distinction and univalence,
/// it proves that symbolic distinction is equal to univalence.
#[cfg(feature = "quantify")]
pub trait SymbolicDistinction: Pred {
    /// Definition of symbolic distinction.
    fn def<A: Prop, B: Prop>() -> Eq<App2<Self, A, B>, EqQ<A, B>>;

    fn from_eqq<A: Prop, B: Prop>(eqq: EqQ<A, B>) -> App2<Self, A, B> {
        Self::def().1(eqq)
    }
    fn to_eq_eq_q<A: Prop, B: Prop>(x: App2<Self, A, B>) -> Eq<Eq<A, B>, Q<A, B>> {
        (Self::def().0(x), Rc::new(move |q_ab| quality::to_eq(q_ab)))
    }
    fn from_eq_eq_q<A: Prop, B: Prop>(eq_eq_q: Eq<Eq<A, B>, Q<A, B>>) -> App2<Self, A, B> {
        let eq_q = eq_eq_q.0;
        Self::from_eqq(eq_q)
    }
    fn to_univ<A: Prop, B: Prop>(x: App2<Self, A, B>) -> Univ<A, B> {
        univalence::eq_lift(Self::to_eq_eq_q(x))
    }
    fn from_univ<A: Prop, B: Prop>(y: Univ<A, B>) -> App2<Self, A, B> {
        Self::from_eq_eq_q(quality::to_eq(y))
    }
    fn eq_def<A: Prop, B: Prop>() -> Eq<App2<Self, A, B>, Eq<Eq<A, B>, Q<A, B>>> {
        (Rc::new(move |x| Self::to_eq_eq_q(x)), Rc::new(move |y| Self::from_eq_eq_q(y)))
    }

    /// Proves that the definition is the same as univalence.
    /// Therefore, symbolic distiction equals univalence.
    fn univ_def<A: Prop, B: Prop>() -> Eq<App2<Self, A, B>, Univ<A, B>> {
        eq::in_right_arg(Self::eq_def(), (
            Rc::new(move |x| univalence::eq_lift(x)),
            Rc::new(move |y| quality::to_eq(y))
        ))
    }
}

fn main() {}
