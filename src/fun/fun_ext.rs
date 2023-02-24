//! # Function Extensionality
//!
//! It is possible to prove the following (`fun_ext`):
//!
//! `(f == g)^true => fun_ext_ty(f, g)`
//!
//! However, the reverse is not possible to prove.
//!
//! By using path semantical quality, the `path` axiom makes it possible to get the inverse map:
//!
//! `theory(f) ⋀ ~inv(f) ⋀ (f : x -> y) ⋀ (x -> y)  =>  f ⋀ inv(f)`
//!
//! Which proves (`path_inv`):
//!
//! `theory(f) ⋀ ~inv(f) ⋀ (f : x -> y) ⋀ (x -> y)  =>  (y -> x)`
//!
//! Here, `theory(f)` means the type `f : x -> y` needs to be some definition.
//! Otherwise, it would be possible to use `~true` to get `y -> x` from all `x -> y`.
//!
//! This means, only `~inv(fun_ext(f, g))` needs to be added,
//! together with declaration of the type of function extensionality:
//!
//! `fun_ext(f, g) : (f == g)^true -> fun_ext_ty(f, g)`
//!
//! The `path` axiom might be thought of as collapsing the proof space of all
//! tautology transforms with inverses, together with the proof space of inverses.
//! With other words, it leverages PSI to say that any proof of `x -> y` is identical to having a
//! proof of `y -> x` when there exists an inverse and a proof `f : x -> y`.

use super::*;

/// `(\(a : x) = (f(a) == g(a))) . (snd . snd)`.
pub type FunExtAppEq<F, G, A, X> = Comp<Lam<Ty<A, X>, Eq<App<F, A>, App<G, A>>>, Comp<Snd, Snd>>;

/// `((f, g, a) : (x -> y, x -> y, x)) -> ((\(a : x) = (f(a) == g(a))) . (snd . snd))((f, g, a))`.
///
/// Function extensionality type.
pub type FunExtTy<F, G, X, Y, A> = DepFunTy<
    Tup3<F, G, A>, Tup3<Pow<Y, X>, Pow<Y, X>, X>,
    FunExtAppEq<F, G, A, X>,
>;
/// Function extensionality.
#[derive(Copy, Clone)]
pub struct FunExt(());

/// `fun_ext(f, g) : (f == g)^true -> fun_ext_ty(f, g)`.
///
/// Type of function extensionality.
pub fn fun_ext_ty<F: Prop, G: Prop, X: Prop, Y: Prop, A: Prop>() ->
    Ty<App<FunExt, Tup<F, G>>, Pow<FunExtTy<F, G, X, Y, A>, Tauto<Eq<F, G>>>>
{unimplemented!()}
/// `~inv(fun_ext(f, g))`.
pub fn qu_inv_fun_ext<F: Prop, G: Prop>() -> Qu<Inv<App<FunExt, Tup<F, G>>>> {unimplemented!()}

/// `(a : x) ⋀ (f == g)  =>  ((\(a : x) = (f(a) == g(a))) . (snd . snd))((f, g, a))`.
pub fn fun_ext_app_eq_from_eq<F: Prop, G: Prop, A: Prop, X: Prop>(
    ty_a: Ty<A, X>,
    eq: Eq<F, G>
) -> App<FunExtAppEq<F, G, A, X>, Tup3<F, G, A>> {
    let x = app_map_eq(comp_eq_left(lam_eq_lift(ty_a.clone(),
        (True.map_any(), app_map_eq(eq).map_any()))));
    let x = eq::transitivity(x, eq::symmetry(eq_app_comp()));
    let x = eq::transitivity(x, app_eq(eq::symmetry(eq_app_comp())));
    let x = eq::transitivity(eq::transitivity(x, app_eq(app_eq(snd_def()))), app_eq(snd_def()));
    eq::transitivity(x, eq::transitivity(lam(ty_a), subst_nop())).1(True)
}
/// `(f == g)^true => fun_ext_ty(f, g)`.
pub fn fun_ext<F: Prop, G: Prop, X: Prop, Y: Prop, A: Prop>(
    tauto_eq_fg: Tauto<Eq<F, G>>
) -> FunExtTy<F, G, X, Y, A> {
    use path_semantics::ty_eq_left;
    use hooo::{hooo_eq, hooo_imply, pow_eq_right, pow_transitivity, tauto_eq_symmetry, tr};

    fn g<F: Prop, G: Prop>(x: Eq<F, G>) -> Eq<Eq<F, F>, Eq<F, G>> {
        (x.map_any(), eq::refl().map_any())
    }
    fn h<A: Prop, B: Prop, C: Prop, X: Prop>(ty_a: Ty<A, X>) ->
        Imply<Eq<B, C>, Eq<Lam<Ty<A, X>, B>, Lam<Ty<A, X>, C>>>
    {Rc::new(move |x| lam_eq_lift(ty_a.clone(), x))}

    let x = hooo_imply(h)(hooo::tr().trans(tauto_eq_fg.trans(app_map_eq).trans(g)))
        .trans(comp_eq_left).trans(app_map_eq);
    let y = {
        let x = tauto_eq_symmetry(tauto_eq_fg).trans(tup3_eq_snd);
        eq::transitivity(hooo_eq(tr().trans(x.trans(app_eq))), pow_eq_right(x.trans(ty_eq_left)))
    };
    eq::in_left_arg(hooo_eq(pow_transitivity(tup3_trd, x)), y).0(fun_ext_refl())
}
/// `fun_ext_ty(f, g) => (f == g)^true`.
pub fn fun_rev_ext<F: Prop, G: Prop, X: Prop, Y: Prop, A: Prop>(
    x: FunExtTy<F, G, X, Y, A>
) -> Tauto<Eq<F, G>> {path_inv(app_theory(), qu_inv_fun_ext(), fun_ext_ty(), fun_ext)(x)}
/// `(a : x)  =>  ((\(a : x) = (f(a) == f(a))) . (snd . snd))((f, f, a))`.
pub fn fun_ext_app_eq_refl<F: Prop, A: Prop, X: Prop>(
    ty_a: Ty<A, X>
) -> App<FunExtAppEq<F, F, A, X>, Tup3<F, F, A>> {fun_ext_app_eq_from_eq(ty_a, eq::refl())}
/// `fun_ext_ty(f, f)`.
pub fn fun_ext_refl<F: Prop, X: Prop, Y: Prop, A: Prop>() -> FunExtTy<F, F, X, Y, A> {
    hooo::pow_transitivity(tup3_trd, fun_ext_app_eq_refl)
}
/// `fun_ext_ty(f, g) => fun_ext_ty(g, f)`.
pub fn fun_ext_symmetry<F: Prop, G: Prop, X: Prop, Y: Prop, A: Prop>(
    x: FunExtTy<F, G, X, Y, A>
) -> FunExtTy<G, F, X, Y, A> {fun_ext(hooo::tauto_eq_symmetry(fun_rev_ext(x)))}
/// `fun_ext_ty(f, g) ⋀ fun_ext_ty(g, h)  =>  fun_ext_ty(f, h)`.
pub fn fun_ext_transitivity<F: Prop, G: Prop, H: Prop, X: Prop, Y: Prop, A: Prop>(
    fun_ext_fg: FunExtTy<F, G, X, Y, A>,
    fun_ext_gh: FunExtTy<G, H, X, Y, A>,
) -> FunExtTy<F, H, X, Y, A> {
    let fg = fun_rev_ext(fun_ext_fg);
    let gh = fun_rev_ext(fun_ext_gh);
    fun_ext(hooo::tauto_eq_transitivity(fg, gh))
}
