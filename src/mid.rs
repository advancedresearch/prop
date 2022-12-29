//! # Middle Exponential Propositions
//!
//! By building on Existential Logic and Exponential Propositions (HOOO),
//! it is possible to talk about nuances of middle propositions.
//!
//! All middle exponential propositions implies a theory (in HOOO EP).
//!
//! ### Up, Down and Middle
//!
//! The basic middle exponential propositions are:
//!
//! ```text
//! up(a) = (¬¬a ⋀ ¬(a^true))
//! down(a) = (¬a ⋀ ¬(false^a))
//! mid(a) = up(a) ⋁ down(a)
//! ```
//!
//! - The `up(a)` proposition is close to `a^true`
//! - The `down(a)` proposition is close to `false^a`
//! - The `mid(a)` proposition is close to `theory(a)`
//!
//! ### Lifting existential propositions to middle exponential propositions
//!
//! `theory(a) => mid(a)`
//!
//! This theorem is provable when `¬¬a ⋁ ¬a` (Excluded Middle of Non-Existence).

use crate::*;
use existence::*;
use hooo::*;

/// `(¬¬a ⋀ ¬(a^true))`.
pub type Up<A> = And<Not<Not<A>>, Not<Tauto<A>>>;
/// `(¬a ⋀ ¬(false^a))`.
pub type Down<A> = And<Not<A>, Not<Para<A>>>;
/// A middle proposition `(¬¬a ⋀ ¬(a^true)) ⋁ (¬a ⋀ ¬(false^a))`.
pub type Mid<A> = Or<Up<A>, Down<A>>;

/// `theory(a) => mid(a)`.
pub fn theory_to_mid<A: EProp>(th_a: Theory<A>) -> Mid<A> {
    let (ntauto_a, npara_a) = and::from_de_morgan(th_a);
    match A::e() {
        Left(nna) => Left((nna, ntauto_a)),
        Right(na) => Right((na, npara_a)),
    }
}

/// `mid(a) => theory(a)`.
pub fn mid_to_theory<A: Prop>(ma: Mid<A>) -> Theory<A> {
    match ma {
        Left((nna, ntauto_a)) => nn_not_tauto_to_theory(nna, ntauto_a),
        Right((na, npara_a)) => n_not_para_to_theory(na, npara_a),
    }
}

/// `up(a) => ¬down(a)`.
pub fn up_to_not_down<A: Prop>(up: Up<A>) -> Not<Down<A>> {
    Rc::new(move |down| up.clone().0(down.0))
}

/// `down(a) => ¬up(a)`.
pub fn down_to_not_up<A: Prop>(down: Down<A>) -> Not<Up<A>> {
    Rc::new(move |up| up.0(down.clone().0))
}
