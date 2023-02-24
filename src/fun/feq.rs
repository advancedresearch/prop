use super::*;
use bool_alg::*;
use phott::*;

/// Composable equality.
#[derive(Copy, Clone)]
pub struct FEq(());

/// `eq{x}(a, b)`.
pub type Equal<X, A, B> = App<App<FEq, X>, Tup<A, B>>;

/// `t : type(0)  =>  eq{t} : t x t -> bool`.
pub fn equal_ty<T: Prop>(_ty_t: Ty<T, Type<Z>>) -> Ty<App<FEq, T>, Pow<Bool, Tup<T, T>>> {
    unimplemented!()
}
/// `is_const(eq)`.
pub fn implicit_equal_is_const() -> IsConst<FEq> {unimplemented!()}
/// `is_const(eq{t})`.
pub fn equal_is_const<T: Prop>(_: IsConst<T>) -> IsConst<App<FEq, T>> {unimplemented!()}
/// `a : x  =>  eq{x}(a, a) = tr`.
pub fn equal_refl<X: Prop, A: Prop>(_ty_a: Ty<A, X>) -> Eq<Equal<X, A, A>, Tr> {unimplemented!()}
/// `eq{x}(a, b) = tr  =>  eq{x}(b, a) = tr`.
pub fn equal_symmetry<X: Prop, A: Prop, B: Prop>(_: Equal<X, A, B>) -> Equal<X, B, A> {
    unimplemented!()
}
/// `(eq{x}(a, b) = tr) ⋀ (eq{x}(b, c) = tr)  =>  (eq{x}(a, c) = tr)`.
pub fn equal_transitivity<X: Prop, A: Prop, B: Prop, C: Prop>(
    _: Equal<X, A, B>,
    _: Equal<X, B, C>
) -> Equal<X, A, C> {unimplemented!()}
/// `(a : x) ⋀ (b : x) ⋀ false^(a == b)  =>  eq{x}(a, b) = fa`.
pub fn equal_from_para_eq<X: Prop, A: Prop, B: Prop>(
    _: Ty<A, X>,
    _: Ty<B, X>,
    _: Para<Eq<A, B>>
) -> Eq<Equal<X, A, B>, Fa> {unimplemented!()}

/// `(a : x) ⋀ (a == b)  =>  eq{x}(a, b) = tr`.
pub fn equal_lift<X: Prop, A: Prop, B: Prop>(
    ty_a: Ty<A, X>,
    x: Eq<A, B>
) -> Eq<Equal<X, A, B>, Tr> {
    eq::eq_left(app_eq(tup_eq_snd(x))).0(equal_refl(ty_a))
}
/// `eq{x}(a, b) = fa  =>  ¬(a == b)`.
pub fn equal_fa_lower<X: Prop, A: Prop, B: Prop>(
    ty_a: Ty<A, X>,
    x: Eq<Equal<X, A, B>, Fa>
) -> Not<Eq<A, B>> {
    Rc::new(move |eq_ab| para_eq_tr_fa(eq::in_left_arg(x.clone(),
        equal_lift(ty_a.clone(), eq_ab))))
}
/// `(a : x)^true ⋀ (a == b)^true  =>  (eq{x}(a, b) = tr)^true`.
pub fn tauto_eq_to_tauto_equal<X: Prop, A: Prop, B: Prop>(
    ty_a: Tauto<Ty<A, X>>,
    tauto_eq_ab: Tauto<Eq<A, B>>
) -> Tauto<Eq<Equal<X, A, B>, Tr>> {
    fn f<X: Prop, A: Prop, B: Prop>(
        (ty_a, eq_ab): And<Ty<A, X>, Eq<A, B>>
    ) -> Eq<Equal<X, A, B>, Tr> {equal_lift(ty_a, eq_ab)}
    hooo::hooo_rev_and((ty_a, tauto_eq_ab)).trans(f)
}
/// `(a : x)^true ⋀ is_contr(a == b)  =>  is_contr(eq{x}(a, b) = tr)`.
pub fn is_contr_eq_to_is_contr_equal<X: Prop, A: Prop, B: Prop>(
    ty_a: Tauto<Ty<A, X>>,
    is_contr_eq_ab: IsContr<Eq<A, B>>
) -> IsContr<Eq<Equal<X, A, B>, Tr>> {
    tauto_to_is_contr(tauto_eq_to_tauto_equal(ty_a, is_contr_to_tauto(is_contr_eq_ab)))
}
