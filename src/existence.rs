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

/// Proves that any Catuṣkoṭi with relative excluded middle is absurd.
///
/// A Catuṣkoṭi is a 4-value logic.
/// For more information, see https://en.wikipedia.org/wiki/Catu%E1%B9%A3ko%E1%B9%ADi
pub fn catuskoti_excm_absurd<A: Prop, B: Prop>(
    catus: Not<Eq<ExcM<A>, ExcM<B>>>
) -> False {
    let catus2 = catus.clone();
    let a_nexcm_b: Imply<A, Not<ExcM<B>>> =
        Rc::new(move |a| {
            let catus2 = catus2.clone();
            Rc::new(move |excm_b| {
                let eq = (excm_b.map_any(), Left(a.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let catus2 = catus.clone();
    let na_nexcm_b: Imply<Not<A>, Not<ExcM<B>>> =
        Rc::new(move |na| {
            let catus2 = catus2.clone();
            Rc::new(move |excm_b| {
                let eq = (excm_b.map_any(), Right(na.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let a_nexcm_b2 = a_nexcm_b.clone();
    let a_nb: Imply<A, Not<B>> =
        Rc::new(move |a| {
            let nexcm_b = a_nexcm_b2(a);
            Rc::new(move |b| nexcm_b(Left(b)))
        });
    let a_nnb: Imply<A, Not<Not<B>>> =
        Rc::new(move |a| {
            let nexcm_b = a_nexcm_b(a);
            Rc::new(move |nb| nexcm_b(Right(nb)))
        });
    let na: Not<A> = Rc::new(move |a| a_nnb(a.clone())(a_nb(a)));
    let na2 = na.clone();
    let nb: Not<B> = Rc::new(move |b| na_nexcm_b(na2.clone())(Left(b)));
    let eq: Eq<ExcM<A>, ExcM<B>> = (Right(nb).map_any(), Right(na).map_any());
    catus(eq)
}

/// Proves that any Catuṣkoṭi with relative excluded middle of non-existence is absurd.
///
/// A Catuṣkoṭi is a 4-value logic.
/// For more information, see https://en.wikipedia.org/wiki/Catu%E1%B9%A3ko%E1%B9%ADi
pub fn catuskoti_e_absurd<A: Prop, B: Prop>(
    catus: Not<Eq<E<A>, E<B>>>
) -> False {
    let catus2 = catus.clone();
    let a_ne_b: Imply<A, Not<E<B>>> =
        Rc::new(move |a| {
            let catus2 = catus2.clone();
            Rc::new(move |e_b| {
                let eq = (e_b.map_any(), Left(not::double(a.clone())).map_any());
                catus2.clone()(eq)
            })
        });
    let catus2 = catus.clone();
    let na_ne_b: Imply<Not<A>, Not<E<B>>> =
        Rc::new(move |na| {
            let catus2 = catus2.clone();
            Rc::new(move |e_b| {
                let eq = (e_b.map_any(), Right(na.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let a_ne_b2 = a_ne_b.clone();
    let a_nb: Imply<A, Not<B>> =
        Rc::new(move |a| {
            let ne_b = a_ne_b2(a);
            Rc::new(move |b| ne_b(Left(not::double(b))))
        });
    let a_nnb: Imply<A, Not<Not<B>>> =
        Rc::new(move |a| {
            let ne_b = a_ne_b(a);
            Rc::new(move |nb| ne_b(Right(nb)))
        });
    let na: Not<A> = Rc::new(move |a| a_nnb(a.clone())(a_nb(a)));
    let na2 = na.clone();
    let nb: Not<B> = Rc::new(move |b| na_ne_b(na2.clone())(Left(not::double(b))));
    let eq: Eq<E<A>, E<B>> = (Right(nb).map_any(), Right(na).map_any());
    catus(eq)
}
