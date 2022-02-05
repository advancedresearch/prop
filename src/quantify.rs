//! # Quantifiers
//!
//! This module contains traits for emulating predicates with
//! for-all (`All`) and there-exists (`Any`) quantifiers.

use crate::*;

/// Apply a single argument to predicate.
pub type App<P, A> = <P as Pred>::Out<A>;
/// Apply two arguments to predicate.
pub type App2<P, A, B> = <P as Pred>::Out<And<A, B>>;

/// Implemented by predicates.
pub trait Pred: 'static + Clone {
    /// The output proposition.
    type Out<A: Prop>: Prop;
}

/// Implemented for predicates with a reflexivity property.
pub trait Reflexivity: Pred {
    /// `∀ a { p(a, a) }`.
    fn refl<A: Prop>(&self) -> Self::Out<And<A, A>>;
}

/// Implemented for predicates with an irreflexivity property.
pub trait Irreflexivity: Pred {
    /// `∀ a { ¬p(a, a) }`.
    fn irrefl<A: Prop>(&self) -> Not<Self::Out<And<A, A>>>;
}

/// Implemented for predicates with a symmetry property.
pub trait Symmetry: Pred {
    /// `∀ a, b { p(a, b) => p(b, a) }`.
    fn symmetry<A: Prop, B: Prop>(&self) -> Imply<App2<Self, A, B>, App2<Self, B, A>>;
}

/// Implemented for predicates with an antisymmetry property.
pub trait Antisymmetry: Pred {
    /// `∀ a, b { p(a, b) ⋀ p(b, a) => (a == b) }`.
    fn antisymmetry<A: Prop, B: Prop>(&self) ->
        Imply<And<App2<Self, A, B>, App2<Self, B, A>>, Eq<A, B>>;
}

/// Implemented for predicates with an asymmetry property.
pub trait Asymmetry: Pred {
    /// `∀ a, b { p(a, b) => ¬p(b, a) }`.
    fn asymmetry<A: Prop, B: Prop>(&self) -> Imply<App2<Self, A, B>, Not<App2<Self, B, A>>>;
}

/// Implemented for predicates with a transitivity property.
pub trait Transitivity: Pred {
    /// `∀ a, b, c { p(a, b) ⋀ p(b, c) => p(a, c) }`.
    fn transitivity<A: Prop, B: Prop, C: Prop>(&self) ->
        Imply<And<App2<Self, A, B>, App2<Self, B, C>>, App2<Self, A, C>>;
}

/// Implemented for predicates with a connectivity property.
pub trait Connectivity: Pred {
    /// `∀ a, b { (a ¬= b) => p(a, b) ⋁ p(b, a) }`.
    fn connectivity<A: Prop, B: Prop>(&self) ->
        Imply<Not<Eq<A, B>>, Or<App2<Self, A, B>, App2<Self, B, A>>>;
}

/// Implemented for predicates with a strong connectivity property.
pub trait StrongConnectivity: Pred {
    /// `∀ a, b { p(a, b) ⋁ p(b, a) }`.
    fn strong_connectivity<A: Prop, B: Prop>(&self) -> Or<App2<Self, A, B>, App2<Self, B, A>>;
}

/// Represents a for-all quantifier.
pub trait All<P: Pred>: Prop {
    /// Apply to some argument.
    fn all<A: Prop>(&self) -> App<P, A>;
}

/// Compose two predicates with implication.
#[derive(Clone)]
pub struct PImply<B: Pred, C: Pred>(std::marker::PhantomData<(B, C)>);

impl<B: Pred, C: Pred> Pred for PImply<B, C> {
    type Out<A: Prop> = Imply<App<B, A>, App<C, A>>;
}

impl<P: Pred> All<PImply<P, P>> for () {
    fn all<A: Prop>(&self) -> Imply<App<P, A>, App<P, A>> {
        Rc::new(move |pa| pa)
    }
}

/// Represents a there-exists quantifier.
pub trait Any<B: Pred>: Prop {
    /// `∃ x : A { B(x) } <=> ∀ C : P { ∀ x : A { B(x) => C(x) } => C }`.
    ///
    /// Uses the definition of the existential quantifier
    /// from [Calculus of Constructions](https://en.wikipedia.org/wiki/Calculus_of_constructions).
    fn any<C: Pred>(&self, f: impl All<PImply<B, C>>) -> C;
}

/// Wraps a proposition as a predicate.
///
/// This is used with `Any` to define a finite set of propositions.
#[derive(Clone)]
pub struct Singleton<X: Prop>(pub X);

impl<X: Prop> Pred for Singleton<X> {
    type Out<A: Prop> = X;
}
