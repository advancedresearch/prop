//! # Symbolic Distinction
//!
//! This model is derived from HOOO EP.
//!
//! When one expresses `a == b` in logic, there is no way to prove that `a` and `b`
//! are symbolic distinct, although they are equal.
//! This is because logic treats symbols and values as the same mathematical objects.
//!
//! However, it is possible to prove that `a` is not symbolic distinct from `a` ([not_sd]).
//! Furthermore, it is possible to prove that `false^(a == b)` implies symbolic distinction ([para_eq_to_sd]).
//!
//! Symbolic Distinction [Sd] is defined as:
//!
//! ```text
//! sd(a, b) := ◇(¬(a == b))
//! ```
//!
//! It means, two values are symbolic distinct when it is possible that they are not equal.
//! This is the closest expression in logic that corresponds to symbolic distinction.
//! The definition is based on what can be proved about symbolic distinction.
//!
//! This logical definition is *not* what symbolic distinction means in natural language.
//! Symbolic distinction in natural language uses knowledge about symbolic reasoning that is not
//! accessible within logic, since natural language can reflect upon the symbolic level of
//! abstraction as separated from value level of abstraction.
//!
//! For example, `a` can never be not equal to `a`, so one can prove `¬sd(a, a)`.
//!
//! On the other hand, if we say `a` can never be not equal to `b`, so one can prove `¬sd(a, b)`,
//! then this is provable if `(a == b)^true`. This is because it is not possible for `a` and `b`
//! to be not equal to each other. Yet, this is not the same as when reasoning about symbolic
//! distinction, because everybody can tell `a` is obviously symbolic distinct from `b`.
//!
//! Symbolic Distinction is a valid extension of normal logic to reason about symbolic knowledge.
//! An important property of Symbolic Distinction is that logical reasoning about symbolic
//! distinction is limited. The logical reasoning is only sound, that is overlapping with reasoning
//! about symbolic distinction in natural language, when one talks about: Symbolic Distinction.
//!
//! If this sounds confusing, then remember you are not the only one who get confused by this.
//! The trick is that Symbolic Indistinction is unsound, because if one symbol is not equal to
//! another symbol and yet they are symbolic indistinct, then reasoning is unsound.
//! Under Symbolic Distiction, however, there is no such case where reasoning is unsound.
//! For more information, see [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/symbolic-distinction.pdf).
//!
//! This leads to a case where one can use Symbolic Distinction as a "one sided" theory.
//! The theory has no "other side", kind of like a Möbius strip.
//! It is sound to introduce new operators to logic which semantics depend on Symbolic Distinction.
//!
//! In Path Semantics, this is leveraged to lift `a == b` into `a ~~ b` when `a` and `b` are
//! symbolic distinct ([lift_q]). This proof relies on the axiom [hooo::lift_q] which lifts
//! `a == b` into `a ~~ b` when there is a `theory(a == b)`.
//!
//! A theory of equality means that `a == b` is not provable without making any assumptions
//! and that one can not prove `false` from `a == b`.
//! Theory of equality implies symbolic distinction.
//! This is similar to how `false^(a == b)` implies symbolic distinction,
//! but here one can prove `false` from `a == b`.
//! Theory of equality is another way of getting symbolic distinction.
//!
//! Think about `theory(a == b)` as saying that `a == b` is not entirely true, but it is not entirely false either.
//! It depends on the situation under which circumstances `a == b` is true.
//! From `theory(a == b)` one can not say which circumstances makes `a == b` true.
//! One can only deduce that there are some circumstances, but one does not know which circumstances.

use crate::*;
use modal::Pos;
use hooo::Para;
use quality::{EqQ, Q};

/// `sd(a, b) := ◇(¬(a == b))`.
///
/// This equals `(¬(a == b))^true ⋁ ¬((¬(a == b))^true ⋁ false^(¬(a == b)))`.
pub type Sd<A, B> = Pos<Not<Eq<A, B>>>;

/// `¬sd(a, a)`.
pub fn not_sd<A: Prop>() -> Not<Sd<A, A>> {
    fn f<A: Prop>(neq_aa: Not<Eq<A, A>>) -> False {neq_aa(eq::refl())}
    Rc::new(move |sd_aa| {
        match sd_aa {
            Left(tauto_neq_aa) => tauto_neq_aa(True)(eq::refl()),
            Right(theory_neq_aa) => theory_neq_aa(Right(f)),
        }
    })
}

/// `false^(a == b)  =>  sd(a, b)`.
pub fn para_eq_to_sd<A: Prop, B: Prop>(para_eq_ab: Para<Eq<A, B>>) -> Sd<A, B> {
    Left(hooo::para_to_tauto_not(para_eq_ab))
}

/// `sd(a, ¬a)`.
pub fn sd_not<A: Prop>() -> Sd<A, Not<A>> {para_eq_to_sd(eq::anti)}

/// `(a == b) ⋀ sd(a, b)  =>  (a ~~ b)`.
pub fn lift_q<A: Prop, B: Prop>(eq_ab: Eq<A, B>, sd_ab: Sd<A, B>) -> Q<A, B> {
    match sd_ab {
        Left(tauto_neq_ab) => not::absurd(tauto_neq_ab(True), eq_ab),
        Right(theory_neq_ab) => hooo::lift_q(eq_ab, hooo::theory_not_to_theory(theory_neq_ab)),
    }
}

/// `sd(a, b)  =>  ((a == b) => (a ~~ b))`.
pub fn to_eqq<A: Prop, B: Prop>(sd_ab: Sd<A, B>) -> EqQ<A, B> {
    Rc::new(move |eq_ab| lift_q(eq_ab, sd_ab.clone()))
}
