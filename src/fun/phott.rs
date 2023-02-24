//! # Propositional Homotopy Type Theory
//!
//! This version of Homotopy Type Theory lends itself toward foundational Path Semantics.
//! Since foundational Path Semantics is propositional, it is natural to call this version
//! "Propositional Homotopy Type Theory" (PHoTT).
//!
//! ### Homotopy Proposition
//!
//! A homotopy proposition is defined as following (using the path semantical qubit operator `~`):
//!
//! ```text
//! is_hprop(0, a) := true
//! is_hprop(succ(n), a) := (qubit^succ(n)(a) == qubit^n(a))^true
//! ```
//!
//! For example, `is_prop(a) := is_hprop(1, a)` which equals `(~a == a)^true`.
//!
//! One can prove `is_prop(true)` and `is_prop(false)`.
//!
//! The homotopy level `n` of `is_hprop(n, a)` tells at which level applying the qubit operator
//! `~` contracts to a lower homotopy level.
//!
//! For example, `is_set(a) := is_hprop(2, a)` which equals `(~~a == ~a)^true`.
//!
//! This means, if one has `~~a` or higher, one can contract this to `~a`.
//!
//! ### Interpration of qubit `~`
//!
//! The normal interpretation of homotopy levels in Homotopy Type Theory is to consider paths
//! between paths in some space, which is called a "homotopy".
//!
//! For example, if `p : id{x}(a, b)` and `q : id{x}(a, b)`,
//! then a homotopy `h` is `h : id{id{x}(a, b)}(p, q)`.
//!
//! However, in Path Semantics it is more common to think about homotopy as a propositional
//! equivalence of hypertoruses. Instead of constructing two paths `p, q` from `a` to `b`,
//! one constructs two loops `~a` and `~b` which are then made equal `~a == ~b`.

use super::*;

/// `is_contr(a) := is_hprop(0, a)`.
pub type IsContr<A> = IsHProp<Z, A>;
/// `is_prop(a) := (~a == a)^true`.
pub type IsProp<A> = Tauto<Eq<Qu<A>, A>>;
/// `is_set(a) := is_prop(~a)`.
///
/// This is the same as `(~~a == ~a)^true`.
pub type IsSet<A> = IsProp<Qu<A>>;
/// `is_groupoid(a) := is_set(~a)`.
///
/// This is the same as `(~~~a == ~~a)^true`.
pub type IsGroupoid<A> = IsSet<Qu<A>>;
/// `is_hprop(n, a) := (qubit^n(a) == qubit^(n-1)(a))^true` where `qubit^(-1)(a) == true`.
pub type IsHProp<N, A> = Tauto<Eq<<S<N> as QuHLev>::Out<A>, <N as QuHLev>::Out<A>>>;
/// `is_ngroupoid(n, a) := is_hprop(n+2, a)`.
pub type IsNGroupoid<N, A> = IsHProp<S<S<N>>, A>;

/// Used to get repeated application of qubit `~` corresponding to homotopy levels.
pub trait QuHLev {
    /// The resulting type.
    type Out<A: Prop>: Prop;
}

impl QuHLev for Z {type Out<A: Prop> = True;}
impl<N: Nat> QuHLev for S<N> {type Out<A: Prop> = Qubit<N, A>;}

/// `is_contr(true)`.
pub fn is_contr_true() -> IsContr<True> {
    tauto!((True.map_any(), Qubit::<Z, True>::from(True).map_any()))
}
/// `is_prop(true)`.
pub fn is_prop_true() -> IsProp<True> {tauto!(eq_qu_true_true())}
/// `is_prop(false)`.
pub fn is_prop_false() -> IsProp<False> {tauto!(eq_qu_false_false())}
/// `a^b  =>  is_prop(a^b)`.
pub fn pow_to_is_prop<A: Prop, B: Prop>(x: Pow<A, B>) -> IsProp<Pow<A, B>> {
    x.lift().trans(pow_to_eq_qu)
}
/// `is_set(id{a})`.
pub fn is_set_id<A: Prop>() -> IsSet<App<FId, A>> {collapse_to_set_right(tauto!(id_q()))}
/// `is_set(not)`.
pub fn is_set_not() -> IsSet<bool_alg::FNot> {collapse_to_set_right(tauto!(bool_alg::not_q()))}
/// `is_contr(a)  =>  (a == true)^true`.
pub fn is_contr_to_tauto_eq_true<A: Prop>(x: IsContr<A>) -> Tauto<Eq<A, True>> {
    fn f<A: Prop>(x: Eq<Qubit<Z, A>, True>) -> Eq<A, True> {
        (True.map_any(), Qubit::<Z, A>::to(x.1(True)).map_any())
    }
    x.trans(f)
}
/// `(a == true)^true  =>  is_contr(a)`.
pub fn tauto_eq_true_to_is_contr<A: Prop>(x: Tauto<Eq<A, True>>) -> IsContr<A> {
    fn f<A: Prop>(x: Eq<A, True>) -> Eq<Qubit<Z, A>, True> {
        (True.map_any(), Qubit::<Z, A>::from(x.1(True)).map_any())
    }
    x.trans(f)
}
/// `is_contr(a)  =>  is_prop(a)`.
pub fn is_contr_to_is_prop<A: Prop>(x: IsContr<A>) -> IsProp<A> {
    use hooo::{tauto_qu_eq, tauto_eq_symmetry, tauto_eq_transitivity as trans};

    let y = is_contr_to_tauto_eq_true(x);
    trans(trans(tauto_qu_eq(y), is_prop_true()), tauto_eq_symmetry(y))
}
/// `is_prop(a)  =>  is_set(a)`.
pub fn is_prop_to_is_set<A: Prop>(x: IsProp<A>) -> IsSet<A> {
    fn f<A: Prop>(x: IsProp<A>) -> Eq<Qu<Qu<A>>, Qu<A>> {
        let x2 = hooo::tauto_eq_symmetry(x.clone());
        (Rc::new(move |y| qubit::in_arg(y, x)), Rc::new(move |y| qubit::in_arg(y, x2)))
    }
    x.lift().trans(f)
}
/// `is_set(a)  =>  is_groupoid(a)`.
pub fn is_set_to_is_groupoid<A: Prop>(x: IsSet<A>) -> IsGroupoid<A> {is_prop_to_is_set(x)}
/// `is_prop(a)  =>  is_groupoid(a)`.
pub fn is_prop_to_is_groupoid<A: Prop>(x: IsProp<A>) -> IsGroupoid<A> {
    is_set_to_is_groupoid(is_prop_to_is_set(x))
}
/// `a^true  =>  is_contr(a)`.
pub fn tauto_to_is_contr<A: Prop>(tauto_a: Tauto<A>) -> IsContr<A> {
    tauto_eq_true_to_is_contr(hooo::tauto_to_eq_true(tauto_a))
}
/// `is_contr(a)  =>  a^true`.
pub fn is_contr_to_tauto<A: Prop>(is_contr_a: IsContr<A>) -> Tauto<A> {
    hooo::tauto_from_eq_true(is_contr_to_tauto_eq_true(is_contr_a))
}
/// `a^true  ==  is_contr(a)`.
pub fn eq_tauto_is_contr<A: Prop>() -> Eq<Tauto<A>, IsContr<A>> {
    hooo::pow_eq_to_tauto_eq((tauto_to_is_contr, is_contr_to_tauto))(True)
}
/// `a^true  =>  is_prop(a)`.
pub fn tauto_to_is_prop<A: Prop>(tauto_a: Tauto<A>) -> IsProp<A> {
    tauto_a.lift().trans(tauto_to_eq_qu)
}
/// `false^a  =>  is_prop(a)`.
pub fn para_to_is_prop<A: Prop>(para_a: Para<A>) -> IsProp<A> {para_a.lift().trans(para_to_eq_qu)}
/// `(f ~~ g)^true  =>  is_set(f)`.
pub fn collapse_to_set_left<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> IsSet<F> {
    x.trans(quality::left).trans(Qu::from_q).lift().trans(tauto_to_eq_qu)
}
/// `(f ~~ g)^true  =>  is_set(g)`.
pub fn collapse_to_set_right<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> IsSet<G> {
    collapse_to_set_left(x.trans(quality::symmetry))
}
/// `(f ~~ g)^true  =>  (~~g == ~~f)^true`.
pub fn collapse_to_eq_qu_2<F: Prop, G: Prop>(
    x: Tauto<Q<F, G>>
) -> Tauto<Eq<Qu<Qu<F>>, Qu<Qu<G>>>> {
    fn h<F: Prop, G: Prop>(q: Q<F, G>) -> Eq<Qu<F>, Qu<G>> {and::to_eq_pos(q.1)}
    hooo::tauto_eq_transitivity(
        hooo::tauto_eq_transitivity(collapse_to_set_left(x.clone()), x.trans(h)),
        hooo::tauto_eq_symmetry(collapse_to_set_right(x)))
}
/// `(f ~~ g)^true  =>  hom_eq(3, f, g)^true`.
pub fn collapse_to_hom_eq_3<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> Tauto<HomEq3<F, G>> {
    use qubit::{normalize, rev_normalize};
    use nat::Two;
    fn h<F: Prop, G: Prop>((a, b): Eq<Qu<Qu<F>>, Qu<Qu<G>>>) -> Eq<Qubit<Two, F>, Qubit<Two, G>> {
        (Rc::new(move |x| normalize(a(rev_normalize(x)))),
         Rc::new(move |x| normalize(b(rev_normalize(x)))))
    }
    hooo::hooo_rev_and((collapse_to_eq_qu_2(x).trans(h), x.trans(univalence::q_to_hom_eq_2)))
}
