use super::*;
use bool_alg::*;

/// Composable equality.
#[derive(Copy, Clone)]
pub struct FEq(());

/// `t : type(0)  =>  eq{t} : t x t -> bool`.
pub fn eq_ty<T: Prop>(_ty_t: Ty<T, Type<Z>>) -> Ty<App<FEq, T>, Pow<Bool, Tup<T, T>>> {
    unimplemented!()
}
/// `is_const(eq)`.
pub fn implicit_eq_is_const() -> IsConst<FEq> {unimplemented!()}
/// `is_const(eq{t})`.
pub fn eq_is_const<T: Prop>(_: IsConst<T>) -> IsConst<App<FEq, T>> {unimplemented!()}
/// `a : x  =>  eq{x}((a, a)) = true`.
pub fn eq_refl<X: Prop, A: Prop>(
    _ty_a: Ty<A, X>
) -> Eq<App<App<FEq, X>, Tup<A, A>>, Tr> {unimplemented!()}

/// `(a == b)  =>  eq{a}((a, b)) = true`.
pub fn eq_lift<X: Prop, A: Prop, B: Prop>(
    ty_a: Ty<A, X>,
    x: Eq<A, B>
) -> Eq<App<App<FEq, X>, Tup<A, B>>, Tr> {
    eq::eq_left(app_eq(tup_eq_snd(x))).0(eq_refl(ty_a))
}
/// `eq{x}((a, b)) = false  =>  ¬(a == b)`.
pub fn eq_fa_lower<X: Prop, A: Prop, B: Prop>(
    ty_a: Ty<A, X>,
    x: Eq<App<App<FEq, X>, Tup<A, B>>, Fa>
) -> Not<Eq<A, B>> {
    Rc::new(move |eq_ab| para_eq_tr_fa(eq::in_left_arg(x.clone(), eq_lift(ty_a.clone(), eq_ab))))
}
