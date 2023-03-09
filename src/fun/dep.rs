//! # Dependent Types
//!
//! [Dependent type theory in nLab](https://ncatlab.org/nlab/show/dependent+type+theory)
//!
//! Dependent types is heavily used in software verification.
//! It is also used as a foundation of mathematics in terms of Homotopy Type Theory.
//!
//! There are two objects that are important for dependent types:
//!
//! - Dependent sum/tuple: `(a, b) : (a : x, p(a))` as `DepTup<A, X, B, P>`
//!     - Formation: `dep_tup_ty_formation`
//!     - Introduction: `dep_tup_intro`
//!     - Elimination: `dep_tup_elim`
//!     - Computation: `fst_def, snd_def`
//! - Dependent product/function: `f : (a : x) -> p(a)` as `DepFun<F, A, X, P>`
//!     - Formation: `dep_fun_ty_formation`
//!     - Introduction: `dep_fun_intro`
//!     - Elimination: `dep_fun_elim`
//!     - Computation: `dep_fun_app`
//!
//! This allows `p(a)` to produce a type depending on previous arguments, hence "dependent type".

use super::*;

/// Dependent function type `(a : x) -> p(a)`.
pub type DepFunTy<A, X, PredP> = Pow<App<PredP, A>, Ty<A, X>>;
/// Dependent function `f : ((a : x) -> p(a))`.
pub type DepFun<F, A, X, PredP> = Ty<F, DepFunTy<A, X, PredP>>;
/// Dependent lambda type `(a : x) => p(a)`.
pub type DepLamTy<A, X, PredP> = Imply<Ty<A, X>, App<PredP, X>>;
/// Dependent lambda `f : ((a : x) => p(a))`.
pub type DepLam<F, A, X, PredP> = Ty<F, DepLamTy<A, X, PredP>>;
/// Dependent tuple type `((a : x), p(a))`.
pub type DepTupTy<A, X, PredP> = Tup<Ty<A, X>, App<PredP, A>>;
/// Dependent tuple `(a, b) : ((a : x), p(a))`.
pub type DepTup<A, X, B, PredP> = Ty<Tup<A, B>, DepTupTy<A, X, PredP>>;

/// `(a < x) ⋀ (b < y)^a  =>  b^a < y^x`.
pub fn dep_fun_pord<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _: POrdProof<A, X>,
    _: Pow<POrdProof<B, Y>, A>
) -> POrdProof<Pow<B, A>, Pow<Y, X>> {unimplemented!()}
/// `(a : x) ⋀ (b : y)^a  =>  b^a : y^x`.
pub fn dep_fun_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _ty_a: Ty<A, X>,
    _ty_b: Pow<Ty<B, Y>, A>
) -> Ty<Pow<B, A>, Pow<Y, X>> {unimplemented!()}
/// `(a < x) ⋀ (b < y)^a  =>  (a, b) < (x, y)`.
pub fn dep_tup_pord<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _: POrdProof<A, X>,
    _: Pow<POrdProof<B, Y>, A>
) -> POrdProof<Tup<A, B>, Tup<X, Y>> {unimplemented!()}
/// `(a : x) ⋀ (b : y)^a  =>  (a, b) : (x, y)`.
pub fn dep_tup_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _ty_a: Ty<A, X>,
    _ty_b: Pow<Ty<B, Y>, A>
) -> Ty<Tup<A, B>, Tup<X, Y>> {unimplemented!()}
/// `f(a)^(a : x)  =>  f(b)^(b : x)`.
pub fn dep_app<F: Prop, X: Prop, A: Prop, B: Prop>(
    _: Pow<App<F, A>, Ty<A, X>>
) -> Pow<App<F, B>, Ty<B, X>> {unimplemented!()}
/// `(f(a)^a)(b)  =>  f(b)`.
pub fn dep_fun_app<F: Prop, A: Prop, B: Prop>(_: App<Pow<App<F, A>, A>, B>) -> App<F, B> {
    unimplemented!()
}

/// `(f : (a : x) -> y(a))  =>  (f : (b : x) -> y(b))`.
fn dep_fun_swap_app_ty<F: Prop, A: Prop, B: Prop, X: Prop, Y: Prop>(
    x: Ty<F, Pow<App<Y, A>, Ty<A, X>>>
) -> Ty<F, Pow<App<Y, B>, Ty<B, X>>> {
    unsafe {path_semantics::ty::in_right_arg(x, (Rc::new(dep_app), Rc::new(dep_app)))}
}
/// `(x : type(0))^true ⋀ (p(a) : type(0))^(a : x)  =>  (((a : x) -> p(a)) : type(0))^true`.
pub fn dep_fun_ty_formation<A: Prop, X: Prop, P: Prop>(
    ty_x: Tauto<Ty<X, Type<Z>>>,
    pow_ty_pa_ty_a: Pow<Ty<App<P, A>, Type<Z>>, Ty<A, X>>
) -> Tauto<Ty<DepFunTy<A, X, P>, Type<Z>>> {
    use hooo::{pow_lift, hooo_rev_and};

    fn f<A: Prop, B: Prop, X: Prop, Y: Prop>((x, y): And<Ty<A, X>, Pow<Ty<B, Y>, A>>) ->
        Ty<Pow<B, A>, Pow<Y, X>> {dep_fun_ty(x, y)}
    fn g<A: Prop, B: Prop>(x: Ty<Pow<B, A>, Pow<Type<Z>, Type<Z>>>) -> Ty<Pow<B, A>, Type<Z>> {
        path_semantics::ty::transitivity(x, fun_type_ty())
    }
    hooo_rev_and((ty_x.trans(judgement_ty), pow_lift(pow_ty_pa_ty_a))).trans(f).trans(g)
}
/// `((a : x) -> (p(a) : y(a)))  =>  ((a -> p(a)) : ((b : x) -> y(b)))^true`.
pub fn dep_fun_intro<A: Prop, B: Prop, X: Prop, Y: Prop, P: Prop>(
    x: Pow<Ty<App<P, A>, App<Y, A>>, Ty<A, X>>
) -> Tauto<DepFun<Pow<App<P, A>, A>, A, X, Y>> {
    use hooo::{pow_transitivity, tauto_hooo_ty};

    let f = |x| unsafe {path_semantics::ty::lower(x)};
    tauto_hooo_ty(pow_transitivity(f, x)).trans(dep_fun_swap_app_ty)
}
/// `(f : (a : x) -> p(a))^true ⋀ (b : x)^true  =>  (f(b) : p(b))^true`
pub fn dep_fun_elim<F: Prop, X: Prop, P: Prop, A: Prop, B: Prop>(
    ty_f: Tauto<DepFun<F, A, X, P>>,
    ty_b: Tauto<Ty<B, X>>
) -> Tauto<Ty<App<F, B>, App<P, B>>> {
    use hooo::hooo_rev_and;

    fn g<F: Prop, A: Prop, X: Prop, Y: Prop>(
        (f, x): And<Ty<F, Pow<Y, Ty<A, X>>>, Ty<A, X>>
    ) -> Ty<App<F, A>, Y> {app_fun_ty(f, unsafe {path_semantics::ty::lift(x)})}
    let x: Tauto<Ty<F, Pow<App<P, B>, Ty<B, X>>>> = ty_f.trans(dep_fun_swap_app_ty);
    hooo_rev_and((x, ty_b)).trans(g::<F, B, X, App<P, B>>)
}
/// `(x : type(0))^true ⋀ (p(a) : type(0))^(a : x)  =>  (((a : x), p(a)) : type(0))^true`.
pub fn dep_tup_ty_formation<A: Prop, X: Prop, P: Prop>(
    ty_x: Tauto<Ty<X, Type<Z>>>,
    pow_ty_pa_ty_a: Pow<Ty<App<P, A>, Type<Z>>, Ty<A, X>>
) -> Tauto<Ty<DepTupTy<A, X, P>, Type<Z>>> {
    use hooo::{pow_lift, hooo_rev_and};

    fn f<A: Prop, B: Prop, X: Prop, Y: Prop>((x, y): And<Ty<A, X>, Pow<Ty<B, Y>, A>>) ->
        Ty<Tup<A, B>, Tup<X, Y>> {dep_tup_ty(x, y)}
    fn g<A: Prop, B: Prop>(x: Ty<Tup<A, B>, Tup<Type<Z>, Type<Z>>>) -> Ty<Tup<A, B>, Type<Z>> {
        path_semantics::ty::transitivity(x, tup_type_ty())
    }
    hooo_rev_and((ty_x.trans(judgement_ty), pow_lift(pow_ty_pa_ty_a))).trans(f).trans(g)
}
/// `(a : x)^true ⋀ (b : p(a))^true  =>  ((a, b) : ((a : x, p(a))))^true`.
pub fn dep_tup_intro<A: Prop, X: Prop, B: Prop, P: Prop>(
    ty_a: Tauto<Ty<A, X>>,
    ty_b: Tauto<Ty<B, App<P, A>>>,
) -> Tauto<DepTup<A, X, B, P>> {
    let f = hooo::hooo_imply(tauto!(Rc::new(move |(ty_a, ty_b)| tup_ty(ty_a, ty_b))));
    let x = hooo::hooo_rev_and((ty_a.trans(|x| unsafe {path_semantics::ty::lift(x)}), ty_b));
    f(x)
}
/// `(t : (x : a, b(x)))^true  =>  (fst(t) : a)^true ⋀ (snd(t) : b(fst(t)))^true`.
pub fn dep_tup_elim<T: Prop, X: Prop, A: Prop, B: Prop>(
    ty_t: Tauto<Ty<T, Tup<Ty<X, A>, App<B, X>>>>
) -> And<Tauto<Ty<App<Fst, T>, A>>, Tauto<Ty<App<Snd, T>, App<B, App<Fst, T>>>>> {
    use hooo::{tauto_eq_symmetry, tauto_in_arg};
    use path_semantics::ty::{eq_left, eq_right, lower};

    let x = ty_t.trans(fst_lower);
    (tauto_in_arg(ty_t.trans(fst), tauto_eq_symmetry(x.trans(eq_left)
        .trans(|x| unsafe {eq_right(x)}))).trans(|x| unsafe {lower(x)}),
     tauto_in_arg(ty_t.trans(snd), tauto_eq_symmetry(x.trans(app_eq)
        .trans(|x| unsafe {eq_right(x)}))))
}
