//! # Type Theoretic Existential Philosophy
//!
//! When reasoning about existence in existential philosophy,
//! one can not assume that one's own existence is of the
//! form of a universal existence.
//!
//! The logical nature of existence is unknown.
//!
//! See this [blog post](https://advancedresearch.github.io/blog/2022-02-16-lets-abandon-the-cogito-and-use-type-theory-instead)
//! for more information.
//!
//! However, one can make a weaker assumption `¬¬a ⋁ ¬a`,
//! which is that either one has a negative negative existence,
//! or one has a negative existence.
//! This assumption is called "Excluded Middle of Non-Existence".
//!
//! Descartes' "I think, therefore I am." might be thought of as
//! "I think, therefore I don't non-exist." in this logic.
//!
//! This logic is abbreviated EP (normal) or EPS (path semantical).
//! One property of these logics is that De Morgan's laws hold,
//! even though the excluded middle is not assumed.
//!
//! It means that it can be absurd if I do not exist,
//! or I might not exist, but I have no proof that I exist or not exist.
//!
//! The reason `¬¬a ⋁ ¬a` is used, is to investigate
//! existential philosophy without assuming that the logical nature of existence
//! has something like the excluded middle,
//! yet still allow some reasoning that does not hold in ordinary constructive logic.
//!
//! To assume an existential proposition, use the `EProp` trait.
//!
//! The excluded middle implies an existential proposition.
//! Therefore, a decidable proposition `DProp` automatically implementes `EProp`.

use crate::*;

/// Shorthand for `¬¬x`.
pub type NN<X> = Not<Not<X>>;
/// `∀ x { ¬¬x ⋁ ¬x }`.
pub type E<X> = Or<NN<X>, Not<X>>;
/// `¬¬a == ¬¬b`.
pub type EqNN<A, B> = Eq<NN<A>, NN<B>>;
/// `a =x= b`, defined as `(a => ¬¬b) ⋀ (b => ¬¬a)`.
pub type CrossEq<A, B> = And<Imply<A, NN<B>>, Imply<B, NN<A>>>;

/// Implemented by existential types.
pub trait Existential: Prop {
    /// Get existential rule.
    fn e() -> E<Self>;
}

impl<T: Decidable> Existential for T {
    fn e() -> E<Self> {
        match Self::decide() {
            Left(a) => Left(not::double(a)),
            Right(na) => Right(na),
        }
    }
}

/// Shorthand for existential proposition.
pub trait EProp: Existential {}
impl<T: Existential> EProp for T {}

/// `¬(¬¬a ∧ ¬¬b) => (¬a ∨ ¬b)`.
pub fn or_from_de_morgan<A: EProp, B: EProp>(
    p: Not<And<NN<A>, NN<B>>>
) -> Or<Not<A>, Not<B>> {
    match (A::e(), B::e()) {
        (Left(nna), Left(nnb)) => not::absurd(p, (nna, nnb)),
        (Right(na), _) => Left(na),
        (_, Right(nb)) => Right(nb),
    }
}

/// `(a =x= b) => (¬¬a == ¬¬b)`.
pub fn crosseq_to_eqnn<A: EProp, B: EProp>(cross_eq: CrossEq<A, B>) -> EqNN<A, B> {
    let (ab, ba) = cross_eq;
    match (A::e(), B::e()) {
        (Left(nna), Left(nnb)) => and::to_eq_pos((nna, nnb)),
        (Left(nna), Right(nb)) =>
            not::absurd(nna, imply::modus_tollens(ab)(not::double(nb))),
        (Right(na), Left(nnb)) =>
            not::absurd(nnb, imply::modus_tollens(ba)(not::double(na))),
        (Right(na), Right(nb)) =>
            (
                Rc::new(move |nna| not::absurd(nna, na.clone())),
                Rc::new(move |nnb| not::absurd(nnb, nb.clone())),
            )
    }
}

/// `(¬¬a == ¬¬b) => (a =x= b)`.
pub fn eqnn_to_crosseq<A: Prop, B: Prop>(eq: EqNN<A, B>) -> CrossEq<A, B> {
    let eq2 = eq.clone();
    (
        Rc::new(move |a| eq.0(not::double(a))),
        Rc::new(move |b| eq2.1(not::double(b))),
    )
}

/// `(a =x= b) ⋀ (b =x= c) => (a =x= c)`.
pub fn crosseq_transitivity<A: EProp, B: EProp, C: EProp>(
    ab: CrossEq<A, B>,
    bc: CrossEq<B, C>,
) -> CrossEq<A, C> {
    eqnn_to_crosseq(eq::transitivity(crosseq_to_eqnn(ab), crosseq_to_eqnn(bc)))
}
