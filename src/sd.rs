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
//! In Path Semantics, this is leveraged to lift `a == b` into `a ~~ b` when `a` and `b` are
//! symbolic distinct ([lift_q]).

use crate::*;
use modal::Pos;
use hooo::Para;
use quality::Q;

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
    use hooo::Theory;

    match sd_ab {
        Left(tauto_neq_ab) => not::absurd(tauto_neq_ab(True), eq_ab),
        Right(theory_neq_ab) => {
            let theory_neq_ab_2 = theory_neq_ab.clone();
            let x: Theory<Eq<A, B>> = imply::in_left(theory_neq_ab.clone(), move |x| match x {
                Left(tauto_eq_ab) => not::absurd(theory_neq_ab_2.clone(), Right(hooo::tauto_to_para_not(tauto_eq_ab))),
                Right(para_eq_ab) => Left(hooo::para_to_tauto_not(para_eq_ab))
            });
            hooo::lift_q(eq_ab, x)
        }
    }
}
