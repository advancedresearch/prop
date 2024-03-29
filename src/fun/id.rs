//! # Identity function.
//!
//! ### Qubit Truths
//!
//! The identity `id{a}` ([Id]) has itself as an inverse `inv(id{a}) ~~ id{a}` (see [inv::id_q]).
//! From this, one can prove `~id{a}`. Using `~id{A} : ~(A -> A)` it is possible to prove `~(A -> A)`.
//!
//! Now, it turns out that the proposition `A -> A`, or `A^A`, for any `A` is tautologically true.
//! Therefore, one can prove `~true` ([true_qu]) and as consequence:
//!
//! - `~true == true` ([eq_qu_true_true])
//! - `~false == false` ([eq_qu_false_false])
//!
//! This is amazing because it is a sophisticated result of Path Semantics using
//! PSI/PSQ/HOOO EP and Category Theory. One might expect that fundamental Path Semantics can
//! provide useful mathematical language design, but it is surprising that useful design can
//! provide insights/theorems into fundamental Path Semantics. The theorems above are not provable
//! using PSI/PSQ/HOOO EP alone.
//!
//! The philosophical consequences of the proof of `~true` ([true_qu]) are possibly profound,
//! as discussed in [this blog post](https://advancedresearch.github.io/blog/2023-02-12-the-proof-of-true).

use super::*;

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// `id{t}`.
pub type Id<T> = App<FId, T>;

/// `a : type(n)  =>  id{a} : a -> a`.
///
/// Type of Id.
pub fn id_ty<A: Prop, N: Nat>(_ty_a: Ty<A, Type<N>>) -> Ty<App<FId, A>, Pow<A, A>> {
    unimplemented!()
}
/// `is_const(id)`.
pub fn implicit_id_is_const() -> IsConst<FId> {unimplemented!()}
/// `(x : type(n)) ⋀ (a : x)  =>  id{x}(a) = a`.
///
/// Definition of identity function.
pub fn id_def<A: Prop, X: Prop, N: Nat>(
    _ty_x: Ty<X, Type<N>>,
    _ty_a: Ty<A, X>
) -> Eq<App<Id<X>, A>, A> {unimplemented!()}

/// `is_const(a)  =>  is_const(id{a})`.
pub fn id_is_const<A: Prop>(a_is_const: IsConst<A>) -> IsConst<App<FId, A>> {
    app_is_const(implicit_id_is_const(), a_is_const)
}
/// `a : type(n)  =>  id{type(n)}(a) = a`.
pub fn id_def_type<A: Prop, N: Nat>(ty_a: Ty<A, Type<N>>) -> Eq<App<Id<Type<N>>, A>, A> {
    id_def(type_ty(), ty_a)
}
/// `(a : type(n))^true  =>  theory(a)`.
pub fn theory<A: Prop, N: Nat>(ty_a: Tauto<Ty<A, Type<N>>>) -> Theory<A> {
    hooo::theory_in_arg(app_theory(), ty_a.trans(id_def_type))
}
/// `(a == b) ⋀ ((a == b) : type(n))^true  =>  (a ~~ b)`.
pub fn type_eq_to_q<A: Prop, B: Prop, N: Nat>(
    eq_ab: Eq<A, B>,
    ty_eq_ab: Tauto<Ty<Eq<A, B>, Type<N>>>,
) -> Q<A, B> {hooo::lift_q(eq_ab, theory(ty_eq_ab))}
/// `a : type(n)  =>  ~id{a} : ~(a -> a)`.
pub fn id_qu_ty<A: Prop, N: Nat>(
    ty_a: Ty<A, Type<N>>
) -> Ty<Qu<App<FId, A>>, Qu<Pow<A, A>>> {ty::qu_formation(id_ty(ty_a))}
/// `~id{a}`.
pub fn id_qu<A: Prop>() -> Qu<App<FId, A>> {Qu::from_q(quality::right(id_q()))}
/// `~true`.
pub fn true_qu() -> Qu<True> {
    use bool_alg::Bool;

    // id{bool} : bool -> bool
    let x: Ty<App<FId, Bool>, Pow<Bool, Bool>> = id_ty(bool_alg::bool_ty());

    // ~id{bool} : ~(bool -> bool)
    let x = ty::qu_formation(x);

    // ~(bool -> bool)
    let x: Qu<Pow<Bool, Bool>> = x.0(id_qu());

    // ~true
    let y: Tauto<Eq<Pow<Bool, Bool>, True>> =
        tauto!((True.map_any(), Rc::new(|_| hooo::pow_refl)));
    qubit::in_arg(x, y)
}
/// `~true == true`.
pub fn eq_qu_true_true() -> Eq<Qu<True>, True> {(True.map_any(), true_qu().map_any())}
/// `a  =>  ~a`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [ty::ty_rev_true].
#[deny(unsafe_op_in_unsafe_fn)]
pub unsafe fn to_qu<A: Prop>(a: A) -> Qu<A> {
    use path_semantics::ty::{ty_rev_true, qu_formation, in_left_arg, ty_true};

    ty_true(in_left_arg(qu_formation(unsafe {ty_rev_true(a)}), eq_qu_true_true()))
}
/// `a^true  =>  ~a`.
pub fn tauto_to_qu<A: Prop>(tauto_a: Tauto<A>) -> Qu<A> {
    qubit::in_arg(true_qu(), hooo::pow_eq_to_tauto_eq((tauto_a, hooo::tr())))
}
/// `true : type(n) ⋀ a^b  =>  ~(a^b)`.
pub fn pow_qu<A: Prop, B: Prop>(
    x: Pow<A, B>
) -> Qu<Pow<A, B>> {tauto_to_qu(hooo::pow_lift(x))}
/// `¬~false`.
pub fn not_qu_false() -> Not<Qu<False>> {
    imply::in_left(quality::q_inv_to_sesh(Qu::to_q(qubit::in_arg(true_qu(),
        tauto!((imply::id().map_any(), True.map_any()))))), Qu::to_q)
}
/// `~false == false`.
pub fn eq_qu_false_false() -> Eq<Qu<False>, False> {and::to_eq_neg((not_qu_false(), imply::id()))}
/// `false^a  =>  ¬~a`.
pub fn para_to_not_qu<A: Prop>(para_a: Para<A>) -> Not<Qu<A>> {
    imply::in_left(not_qu_false(),
        move |y| qubit::in_arg(y, hooo::pow_eq_to_tauto_eq((para_a, hooo::fa()))))
}
/// `a^true  =>  (~a == a)`.
pub fn tauto_to_eq_qu<A: Prop>(tauto_a: Tauto<A>) -> Eq<Qu<A>, A> {
    (tauto_a(True).map_any(), tauto_to_qu(tauto_a).map_any())
}
/// `false^a  =>  (~a == a)`.
pub fn para_to_eq_qu<A: Prop>(para_a: Para<A>) -> Eq<Qu<A>, A> {
    (Rc::new(move |qu_a| imply::absurd()(para_to_not_qu(para_a)(qu_a))),
     Rc::new(move |a| imply::absurd()(para_a(a))))
}
/// `a^b  =>  (~(a^b) == a^b)`.
pub fn pow_to_eq_qu<A: Prop, B: Prop>(x: Pow<A, B>) -> Eq<Qu<Pow<A, B>>, Pow<A, B>> {
    tauto_to_eq_qu(x.lift())
}
