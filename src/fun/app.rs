#![deny(unsafe_op_in_unsafe_fn)]

use super::*;

/// Apply 2 function arguments using function currying.
///
/// Function currying means that each argument is applied in turn,
/// instead of applying multiple arguments at once as a tuple.
pub type App2<F, X, Y> = App<App<F, X>, Y>;

/// Applied function.
#[derive(Copy, Clone)]
pub struct App<F, X>(F, X);

/// `is_const(f) ⋀ is_const(x)  =>  is_const(f(x))`.
pub fn app_is_const<F: Prop, X: Prop>(_f: IsConst<F>, _x: IsConst<X>) -> IsConst<App<F, X>> {
    unimplemented!()
}
/// `(x == y)  =>  (f(x) == f(y))`.
///
/// Indiscernibility of identicals (Leibniz's law).
pub fn app_eq<F: Prop, X: Prop, Y: Prop>(
    _eq_xy: Eq<X, Y>
) -> Eq<App<F, X>, App<F, Y>> {unimplemented!()}
/// `(f == g)  =>  (f(x) == g(y))`.
///
/// Lift equality of maps to application.
pub fn app_map_eq<F: Prop, G: Prop, X: Prop>(
    _eq_fg: Eq<F, G>
) -> Eq<App<F, X>, App<G, X>> {unimplemented!()}
/// `(f(a) : y)^(a : x)  =>  (f : (x -> y))`.
pub fn app_rev_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _: Pow<Ty<App<F, A>, Y>, Ty<A, X>>
) -> Ty<F, Pow<Y, X>> {unimplemented!()}
/// `(f : (x -> y)) ⋀ (a : x)  =>  (f(a) : y)`.
///
/// Get type of applied function.
pub fn app_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>,
    _ty_a: Ty<A, X>,
) -> Ty<App<F, A>, Y> {unimplemented!()}
/// `(f : (x => y)) ⋀ (a : x)  =>  (f(a) : y)`.
///
/// Get type of applied lambda.
pub fn app_lam_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_f: Ty<F, Imply<X, Y>>,
    _ty_a: Ty<A, X>,
) -> Ty<App<F, A>, Y> {unimplemented!()}
/// `(a : x) ⋀ (f(a) : y)  =>  (f : (x => y))`.
pub fn app_rev_lam_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_a: Ty<A, X>,
    _ty_fa: Imply<Ty<A, X>, Ty<App<F, A>, Y>>
) -> Ty<F, Imply<Y, X>> {unimplemented!()}
/// `(f : (x -> y)) ⋀ (g : (x -> y)) ⋀ (f(a) == g(a))^(a : x)  =>  ∃ a : x { f == g }`.
pub fn app_fun_ext<F: Prop, G: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>,
    _ty_g: Ty<G, Pow<Y, X>>,
    _pow_eq_fa_ga_ty_a: Pow<Eq<App<F, A>, App<G, A>>, Ty<A, X>>
) -> Exists<Ty<A, X>, Eq<F, G>> {unimplemented!()}
/// `theory(f(x))`.
///
/// This prevents polluting functional values with meta-level truths.
pub fn app_theory<F: Prop, X: Prop>() -> Theory<App<F, X>> {unimplemented!()}

/// `(f : x -> y -> z) ⋀ (a : x) ⋀ (b : y)  =>  f(a)(b) : z`.
///
/// Get type of applied binary operator.
pub fn app2_fun_ty<F: Prop, X: Prop, Y: Prop, Z: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<Pow<Z, Y>, X>>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
) -> Ty<App2<F, A, B>, Z> {
    app_fun_ty(app_fun_ty(ty_f, ty_a), ty_b)
}
/// `(f : x => y => z) ⋀ (a : x) ⋀ (b : y)  =>  f(a)(b) : z`.
///
/// Get type of applied binary operator.
pub fn app2_lam_ty<F: Prop, X: Prop, Y: Prop, Z: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Imply<X, Imply<Y, Z>>>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
) -> Ty<App2<F, A, B>, Z> {
    app_lam_ty(app_lam_ty(ty_f, ty_a), ty_b)
}

/// `(f(a) == b) ⋀ (a : x) ⋀ (b : y)  =>  (\(a : x) = f(a)) : (x => y)`.
pub fn app_lift_ty_lam<F: Prop, A: Prop, B: Prop, X: Prop, Y: Prop>(
    x: Eq<App<F, A>, B>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
) -> Ty<Lam<Ty<A, X>, App<F, A>>, Imply<X, Y>> {
    lam_ty(ty_a, path_semantics::ty::in_left_arg(ty_b, eq::symmetry(x)))
}
/// `f : x -> y  =>  f : x => y`.
pub unsafe fn fun_to_lam_ty<F: Prop, X: Prop, Y: Prop>(ty_f: Ty<F, Pow<Y, X>>) -> Ty<F, Imply<X, Y>> {
    let x = hooo::pow_to_imply(hooo::pow_to_imply);
    (imply::transitivity(ty_f.0, x.clone()), unsafe {ty_f.1.by_imply_right(x)})
}
/// `(f(a)^a : x -> y)^true  =>  (f : x -> y)`.
pub fn app_fun_unfold<F: Prop, A: Prop, X: Prop, Y: Prop>(
    ty_f: Tauto<Ty<Pow<App<F, A>, A>, Pow<Y, X>>>,
) -> Ty<F, Pow<Y, X>> {app_rev_fun_ty(hooo::tauto_hooo_rev_ty(ty_f))}
/// `(f : x => y)^true  =>  (f^true : x -> y)`.
pub unsafe fn tauto_lam_to_tauto_fun_ty<F: Prop, X: Prop, Y: Prop>(
    ty_f: Tauto<Ty<F, Imply<X, Y>>>
) -> Ty<Tauto<F>, Pow<Y, X>> {
    use hooo::{tauto_imply_to_imply_tauto_pow, tauto_imply_to_pow, hooo_pord, pow_to_imply};

    (tauto_imply_to_imply_tauto_pow(ty_f.trans(and::fst)),
     unsafe {hooo_pord(ty_f.trans(and::snd)).by_imply_right(pow_to_imply(tauto_imply_to_pow))})
}
/// `(f(a)^a : x => y)^true  =>  (f : x -> y)`.
pub unsafe fn app_tauto_lam_to_tauto_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    ty_f: Tauto<Ty<Pow<App<F, A>, A>, Imply<X, Y>>>
) -> Ty<F, Pow<Y, X>> {
    use hooo::pow_lift;

    let x = hooo::pow_tauto_to_pow_tauto_tauto(|x| unsafe {tauto_lam_to_tauto_fun_ty(x)})(ty_f);
    let y = tauto!(path_semantics::ty::eq_left((Rc::new(|x: Tauto<_>| x(True)), Rc::new(pow_lift))));
    let x = hooo::tauto_in_arg(x, y);
    app_fun_unfold(x)
}
/// `(f(a) : y)^(a : x)  =>  (f(b) : y)^(b : x)`.
pub fn app_fun_swap_ty<F: Prop, X: Prop, Y: Prop, A: Prop, B: Prop>(
    x: Pow<Ty<App<F, A>, Y>, Ty<A, X>>
) -> Pow<Ty<App<F, B>, Y>, Ty<B, X>> {
    fn f<F: Prop, X: Prop, Y: Prop, A: Prop, B: Prop>(ty_b: Ty<B, X>) ->
        Imply<Pow<Ty<App<F, A>, Y>, Ty<A, X>>, Ty<App<F, B>, Y>>
    {Rc::new(move |x| app_fun_ty(app_rev_fun_ty(x), ty_b.clone()))}
    hooo::hooo_imply(f)(hooo::pow_lift(x))
}
