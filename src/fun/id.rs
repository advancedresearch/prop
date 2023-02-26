//! Identity function.

use super::*;

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// `id`.
pub type Id<T, A> = App<App<FId, T>, A>;

/// `id{a} : a -> a`.
///
/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<App<FId, A>, Pow<A, A>> {unimplemented!()}
/// `is_const(id)`.
pub fn implicit_id_is_const() -> IsConst<FId> {unimplemented!()}
/// `(x : type(n)) ⋀ (a : x)  =>  id{x}(a) = a`.
///
/// Definition of identity function.
pub fn id_def<A: Prop, X: Prop, N: Nat>(
    _ty_x: Ty<X, Type<N>>,
    _ty_a: Ty<A, X>
) -> Eq<Id<X, A>, A> {unimplemented!()}
/// `inv(id{x}) == id{x}`.
pub fn id_inv<X: Prop>() -> Eq<Inv<App<FId, X>>, App<FId, X>> {unimplemented!()}
/// `(f : a -> b) ⋀ (f . inv(f))  =>  id{b}`.
pub fn comp_right_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: Comp<F, Inv<F>>
) -> App<FId, B> {unimplemented!()}
/// `(f : a -> b) ⋀ id{b} => (f . inv(f))`.
pub fn id_to_comp_right_inv<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: App<FId, B>
) -> Comp<F, Inv<F>> {unimplemented!()}
/// `(f : a -> b) ⋀ (inv(f) . f) => id{a}`.
pub fn comp_left_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: Comp<Inv<F>, F>
) -> App<FId, A> {unimplemented!()}
/// `(f : a -> b) ⋀ id{a} => (inv(f). f)`.
pub fn id_to_comp_left_inv<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: App<FId, A>
) -> Comp<Inv<F>, F> {unimplemented!()}

/// `is_const(a)  =>  is_const(id{a})`.
pub fn id_is_const<A: Prop>(a_is_const: IsConst<A>) -> IsConst<App<FId, A>> {
    app_is_const(implicit_id_is_const(), a_is_const)
}
/// `a : type(n)  =>  id(a) = a`.
pub fn id_def_type<A: Prop, N: Nat>(ty_a: Ty<A, Type<N>>) -> Eq<Id<Type<N>, A>, A> {
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
/// `(f : A -> B) => ((f ~~ inv(f)) : ((A -> B) ~~ (B -> A)))`.
pub fn self_inv_ty<F: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>
) -> Ty<Q<F, Inv<F>>, Q<Pow<B, A>, Pow<A, B>>> {
    path_semantics::ty_q_formation(ty_f.clone(), inv_ty(ty_f))
}
/// `(f : a -> a) ⋀ (inv(f) == f) => ((f . f) == id{a})`.
pub fn self_inv_to_eq_id<F: Prop, A: Prop>(
    ty_f: Ty<F, Pow<A, A>>,
    eq_f: Eq<Inv<F>, F>
) -> Eq<Comp<F, F>, App<FId, A>> {
    let ty_f_2 = ty_f.clone();
    let eq_f_2 = eq_f.clone();
    (
        Rc::new(move |x| comp_right_inv_to_id(ty_f_2.clone(),
            comp_in_right_arg(x, eq::symmetry(eq_f_2.clone())))),
        Rc::new(move |x| comp_in_right_arg(id_to_comp_right_inv(ty_f.clone(), x), eq_f.clone())),
    )
}
/// `inv(id{a}) ~~ id{a}`.
pub fn id_q<A: Prop>() -> Q<Inv<App<FId, A>>, App<FId, A>> {self_inv_to_q(id_inv())}
/// `~id{a} : ~(a -> a)`.
pub fn id_qu_ty<A: Prop>() -> Ty<Qu<App<FId, A>>, Qu<Pow<A, A>>> {path_semantics::ty_qu_formation(id_ty())}
/// `~id{a}`.
pub fn id_qu<A: Prop>() -> Qu<App<FId, A>> {Qu::from_q(quality::right(id_q()))}
/// `~true`.
pub fn true_qu() -> Qu<True> {
    use path_semantics::{ty_triv, ty_true};

    qubit::in_arg(ty_true(ty_triv(id_qu_ty(), id_qu())),
        tauto!((True.map_any(), Rc::new(|_| hooo::pow_refl::<True>))))
}
/// `~true == true`.
pub fn eq_qu_true_true() -> Eq<Qu<True>, True> {(True.map_any(), true_qu().map_any())}
/// `a^true  =>  ~a`.
pub fn tauto_to_qu<A: Prop>(tauto_a: Tauto<A>) -> Qu<A> {
    qubit::in_arg(true_qu(), hooo::pow_eq_to_tauto_eq((tauto_a, hooo::tr())))
}
/// `a^b  =>  ~(a^b)`.
pub fn pow_qu<A: Prop, B: Prop>(x: Pow<A, B>) -> Qu<Pow<A, B>> {tauto_to_qu(hooo::pow_lift(x))}
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
