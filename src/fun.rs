//! # Functional programming as propositions
//!
//! Model is derived from PSQ, PSI and HOOO EP.
//!
//! ### Types
//!
//! A type `x : T` uses `Ty<X, T>` from the `path_semantics` module (PSI).
//!
//! A function type `f : X -> Y` uses `Ty<F, Pow<Y, X>>` from the `hooo` module (HOOO EP).
//!
//! A lambda/closure type `f : X => Y` uses `Ty<F, Imply<X, Y>>`.
//!
//! ### Imaginary Inverse
//!
//! The syntax `~x` uses `Qu<X>` from the `qubit` module,
//! and the syntax `x ~~ y` uses `Q<X, Y>` from the `quality` module.
//!
//! This model uses [imaginary inverse](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/imaginary-inverse.pdf)
//! `inv(f)` with `~inv(f)` as a proof of bijective inverse.
//! Here, `~` means the path semantical qubit operator, such that:
//!
//! ```text
//! (inv(f) ~~ g) => ~inv(f)
//! ```
//!
//! It means that one uses path semantical quality instead of equality for inverses.
//! Path semantical quality `inv(f) ~~ g` also implies `inv(f) == g`,
//! which is useful in proofs.
//!
//! The `inv_val_qu` axiom makes it possible to compute using the inverse:
//!
//! `(~inv(f) ⋀ (f(x) == y)) => (inv(f)(y) == x)`
//!
//! The reason for this design is that `inv(f) == inv(f)` is a tautology,
//! and Rust's type system can't pattern match on 1-avatars with inequality in rules like in
//! [Avatar Logic](https://github.com/advancedresearch/avalog).
//!
//! By using a partial equivalence operator `~~` instead of `==`,
//! one can not prove `inv(f) ~~ inv(f)` without any assumptions.
//! This solves the problem such that axioms can be added,
//! only for functions that have inverses.
//!
//! If a function `f` has no inverse, it is useful to prove `false^(inv(f) ~~ g)`.

use crate::*;
use path_semantics::{POrdProof, Ty};
use quality::Q;
use qubit::Qu;
use hooo::Pow;
use nat::{Nat, S, Z};

pub mod bool_alg;
pub mod hott;

/// `is_const(a) ⋀ is_const(b)  =>  is_const(a ⋀ b)`.
pub fn and_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<And<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(a ⋁ b)`.
pub fn or_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Or<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(a => b)`.
pub fn imply_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Imply<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(pord(a, b))`.
pub fn pord_is_const<A: Prop, B: Prop>(
    _a: IsConst<A>,
    _b: IsConst<B>
) -> IsConst<POrdProof<A, B>> {
    unimplemented!()
}

/// `is_const(a) ⋀ is_const(b)  =>  is_const(a : b)`.
pub fn ty_is_const<A: Prop, B: Prop>(a: IsConst<A>, b: IsConst<B>) -> IsConst<Ty<A, B>> {
    and_is_const(imply_is_const(a.clone(), b.clone()), pord_is_const(a, b))
}

/// Apply 2 function arguments.
pub type App2<F, X, Y> = App<App<F, X>, Y>;

/// Applied function.
#[derive(Clone)]
pub struct App<F: Prop, X: Prop>(F, X);

/// `is_const(f) ⋀ is_const(x)  =>  is_const(f(x))`.
pub fn app_is_const<F: Prop, X: Prop>(_f: IsConst<F>, _x: IsConst<X>) -> IsConst<App<F, X>> {
    unimplemented!()
}
/// Indiscernibility of identicals (Leibniz's law).
pub fn app_eq<F: Prop, X: Prop, Y: Prop>(
    _eq_xy: Eq<X, Y>
) -> Eq<App<F, X>, App<F, Y>> {unimplemented!()}
/// Lift equality of maps to application.
pub fn app_map_eq<F: Prop, G: Prop, X: Prop>(
    _eq_fg: Eq<F, G>
) -> Eq<App<F, X>, App<G, X>> {unimplemented!()}
/// Get type of applied function.
pub fn app_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>,
    _ty_a: Ty<A, X>,
    _x_is_const: IsConst<X>,
) -> Ty<App<F, A>, Y> {
    unimplemented!()
}
/// `(f : (x => y)) ⋀ (a : x)  =>  (f(a) : y)`.
///
/// Get type of applied lambda.
pub fn app_lam_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _ty_f: Ty<F, Imply<X, Y>>,
    _ty_a: Ty<A, X>,
    _x_is_const: IsConst<X>,
) -> Ty<App<F, A>, Y> {
    unimplemented!()
}
/// `((\(a : x) = b) : (x => y)) ⋀ (a : x) ⋀ (b : y) ⋀ (c : x)  =>  (f(a) : y[a := c])`.
///
/// Get type of applied lambda.
pub fn app_dep_lam_ty<F: Prop, X: Prop, Y: Prop, A: Prop, B: Prop, C: Prop>(
    _ty_f: Ty<Lam<Ty<A, X>, B>, Imply<X, Y>>,
    _ty_a: Ty<A, X>,
    _ty_b: Ty<B, Y>,
    _ty_c: Ty<C, X>,
) -> Ty<App<F, C>, Subst<Y, A, C>> {
    unimplemented!()
}

/// Get type of applied binary operator.
pub fn app2_fun_ty<F: Prop, X: Prop, Y: Prop, Z: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<Pow<Z, Y>, X>>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
    x_is_const: IsConst<X>,
    y_is_const: IsConst<Y>,
) -> Ty<App2<F, A, B>, Z> {
    app_fun_ty(app_fun_ty(ty_f, ty_a, x_is_const), ty_b, y_is_const)
}
/// Get type of applied binary operator.
pub fn app2_lam_ty<F: Prop, X: Prop, Y: Prop, Z: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Imply<X, Imply<Y, Z>>>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
    x_is_const: IsConst<X>,
    y_is_const: IsConst<Y>,
) -> Ty<App2<F, A, B>, Z> {
    app_lam_ty(app_lam_ty(ty_f, ty_a, x_is_const), ty_b, y_is_const)
}

/// `(f(a) == b) ⋀ (a : x) ⋀ (b : y)  =>  (\(a : x) = f(a)) : (x => y)`.
pub fn app_lift_ty_lam<F: Prop, A: Prop, B: Prop, X: Prop, Y: Prop>(
    x: Eq<App<F, A>, B>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
) -> Ty<Lam<Ty<A, X>, App<F, A>>, Imply<X, Y>> {
    lam_ty(ty_a, path_semantics::ty_in_left_arg(ty_b, eq::symmetry(x)))
}

/// Imaginary inverse.
#[derive(Clone)]
pub struct Inv<F: Prop>(F);

/// Inverse type `(f : x -> y) => (inv(f) : y -> x)`.
pub fn inv_ty<F: Prop, X: Prop, Y: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>
) -> Ty<Inv<F>, Pow<X, Y>> {unimplemented!()}
/// `is_const(f) => is_const(inv(f))`.
pub fn inv_is_const<F: Prop>(_a: IsConst<F>) -> IsConst<Inv<F>> {unimplemented!()}
/// Get inverse map of `f` if there exists a proof `~inv(f)`.
pub fn inv_val_qu<F: Prop, A: Prop, B: Prop>(
    _: Qu<Inv<F>>,
    _: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {unimplemented!()}
/// `inv(inv(f)) => f`.
pub fn inv_involve<F: Prop>(_: Inv<Inv<F>>) -> F {unimplemented!()}
/// `f => inv(inv(f))`.
pub fn involve_inv<F: Prop>(_: F) -> Inv<Inv<F>> {unimplemented!()}

/// Get inverse map of `f` if there exists a proof `g`.
///
/// The proof needs to be path semantical quality,
/// since equality is reflexive and this leads to contradiction
/// if values are mutually exclusive.
pub fn inv_val<F: Prop, G: Prop, A: Prop, B: Prop>(
    x: Q<Inv<F>, G>,
    y: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {inv_val_qu(Qu::<Inv<F>>::from_q(quality::left(x)), y)}
/// Get inverse map of `f` by `g`.
pub fn inv_val_other<F: Prop, G: Prop, A: Prop, B: Prop>(
    x: Q<Inv<F>, G>,
    y: Eq<App<F, A>, B>
) -> Eq<App<G, B>, A> {
    eq::in_left_arg(inv_val(x.clone(), y), app_map_eq(quality::to_eq(x)))
}

/// Composition.
#[derive(Clone)]
pub struct Comp<F: Prop, G: Prop>(F, G);

/// Type of composition.
pub fn comp_ty<F: Prop, G: Prop, X: Prop, Y: Prop, Z: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>,
    _ty_g: Ty<G, Pow<Z, Y>>
) -> Ty<Comp<G, F>, Pow<Z, X>> {unimplemented!()}
/// `is_const(f) ⋀ is_const(g)  =>  is_const(g . f)`.
pub fn comp_is_const<F: Prop, G: Prop>(_a: IsConst<F>, _b: IsConst<G>) -> IsConst<Comp<G, F>> {
    unimplemented!()
}
/// `inv(g . f) => (inv(f) . inv(g))`.
pub fn inv_comp_to_comp_inv<F: Prop, G: Prop>(_: Inv<Comp<G, F>>) -> Comp<Inv<F>, Inv<G>> {
    unimplemented!()
}
/// `(inv(f) . inv(g)) => inv(g . f)`.
pub fn comp_inv_to_inv_comp<F: Prop, G: Prop>(_: Comp<Inv<F>, Inv<G>>) -> Inv<Comp<G, F>> {
    unimplemented!()
}
/// `g(f(x)) => (g . f)(x)`.
pub fn app_to_comp<F: Prop, G: Prop, X: Prop>(_: App<G, App<F, X>>) -> App<Comp<G, F>, X> {
    unimplemented!()
}
/// `(g . f)(x) => g(f(x))`.
pub fn comp_to_app<F: Prop, G: Prop, X: Prop>(_: App<Comp<G, F>, X>) -> App<G, App<F, X>> {
    unimplemented!()
}

/// `(g . f)(x) == g(f(x))`.
pub fn eq_app_comp<F: Prop, G: Prop, X: Prop>() -> Eq<App<G, App<F, X>>, App<Comp<G, F>, X>> {
    (Rc::new(move |x| app_to_comp(x)), Rc::new(move |x| comp_to_app(x)))
}
/// `(g . f) ⋀ (g == h)  =>  (h . f)`.
pub fn comp_in_left_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<G, H>) -> Comp<H, F> {
    Comp(y.0(x.0), x.1)
}
/// `(g . f) ⋀ (f == h)  =>  (g . h)`.
pub fn comp_in_right_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<F, H>) -> Comp<G, H> {
    Comp(x.0, y.0(x.1))
}

/// Duplicate function.
#[derive(Clone, Copy)]
pub struct Dup(());

/// Type of Dup.
pub fn dup_ty<A: Prop>() -> Ty<Dup, Pow<Tup<A, A>, A>> {unimplemented!()}
/// is_const(dup).
pub fn dup_is_const() -> IsConst<Dup> {unimplemented!()}

/// Definition of Dup function.
pub fn dup_def<A: Prop>() -> Eq<App<Dup, A>, Tup<A, A>> {unimplemented!()}

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<FId, Pow<A, A>> {unimplemented!()}
/// `is_const(id)`.
pub fn id_is_const() -> IsConst<FId> {unimplemented!()}

/// Definition of identity function.
pub fn id_def<A: Prop>() -> Eq<App<FId, A>, A> {unimplemented!()}
/// `inv(id) ~~ id`.
pub fn id_q() -> Q<Inv<FId>, FId> {unimplemented!()}
/// `(f . inv(f)) => id`.
pub fn comp_right_inv_to_id<F: Prop>(_: Comp<F, Inv<F>>) -> FId {unimplemented!()}
/// `id => (f . inv(f))`.
pub fn id_to_comp_right_inv<F: Prop>(_: FId) -> Comp<F, Inv<F>> {unimplemented!()}
/// `(inv(f) . f) => id`.
pub fn comp_left_inv_to_id<F: Prop>(_: Comp<Inv<F>, F>) -> FId {unimplemented!()}
/// `id => (inv(f). f)`.
pub fn id_to_comp_left_inv<F: Prop>(_: FId) -> Comp<Inv<F>, F> {unimplemented!()}

/// `(f : A -> B) => ((f ~~ inv(f)) : ((A -> B) ~~ (B -> A)))`.
pub fn self_inv_ty<F: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>
) -> Ty<Q<F, Inv<F>>, Q<Pow<B, A>, Pow<A, B>>> {
    path_semantics::ty_q_formation(ty_f.clone(), inv_ty(ty_f))
}
/// `(inv(f) == f) => ((f . f) == id)`.
pub fn self_inv_to_eq_id<F: Prop>(eq_f: Eq<Inv<F>, F>) -> Eq<Comp<F, F>, FId> {
    let eq_f_2 = eq_f.clone();
    (
        Rc::new(move |x| comp_right_inv_to_id(
            comp_in_right_arg(x, eq::symmetry(eq_f_2.clone())))),
        Rc::new(move |x| comp_in_right_arg(id_to_comp_right_inv(x), eq_f.clone())),
    )
}

/// Cumulative type hierarchy.
#[derive(Copy, Clone)]
pub struct Type<N: Nat>(N);

/// `type(n) : type(n+1)`.
pub fn type_ty<N: Nat>() -> Ty<Type<N>, Type<S<N>>> {unimplemented!()}
/// `is_const(type(n))`.
pub fn type_is_const<N: Nat>() -> IsConst<Type<N>> {unimplemented!()}
/// `(a -> b) : type(0)`.
pub fn pow_ty<A: Prop, B: Prop>() -> Ty<Pow<B, A>, Type<Z>> {unimplemented!()}

/// `(f : A -> B) ⋀ (inv(f) ~~ g) => ((f ~~ g) : ((A -> B) ~~ (B -> A)))`.
pub fn q_inv_ty<F: Prop, G: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>,
    q: Q<Inv<F>, G>,
) -> Ty<Q<F, G>, Q<Pow<B, A>, Pow<A, B>>> {
    use quality::transitivity as trans;

    let y = self_inv_ty(ty_f);
    let q2 = q.clone();
    let x: Eq<Q<F, Inv<F>>, Q<F, G>> = (
        Rc::new(move |x| trans(x, q2.clone())),
        Rc::new(move |x| trans(x, quality::symmetry(q.clone())))
    );
    path_semantics::ty_in_left_arg(y, x)
}

/// Tuple.
#[derive(Clone)]
pub struct Tup<A, B>(A, B);

/// `(a : x) ⋀ (b : y)  =>  (a, b) : (x, y)`.
pub fn tup_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _ty_a: Ty<A, X>,
    _ty_b: Ty<B, Y>
) -> Ty<Tup<A, B>, Tup<X, Y>> {unimplemented!()}
/// `is_const(a) ⋀ is_const(b)  =>  is_const((a, b))`.
pub fn tup_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Tup<A, B>> {
    unimplemented!()
}

/// Fst.
#[derive(Copy, Clone)]
pub struct Fst(());

/// Type of Fst.
pub fn fst_ty<A: Prop, B: Prop>() -> Ty<Fst, Pow<A, Tup<A, B>>> {unimplemented!()}
/// `is_const(fst)`.
pub fn fst_is_const() -> IsConst<Fst> {unimplemented!()}
/// `fst((a, b)) = a`.
pub fn fst_def<A: Prop, B: Prop>() -> Eq<App<Fst, Tup<A, B>>, A> {unimplemented!()}

/// Snd.
#[derive(Copy, Clone)]
pub struct Snd(());

/// Type of Snd.
pub fn snd_ty<A: Prop, B: Prop>() -> Ty<Snd, Pow<B, Tup<A, B>>> {unimplemented!()}
/// `is_const(snd)`.
pub fn snd_is_const() -> IsConst<Snd> {unimplemented!()}
/// `snd((a, b)) = b`.
pub fn snd_def<A: Prop, B: Prop>() -> Eq<App<Snd, Tup<A, B>>, B> {unimplemented!()}

/// Substitute in expression.
#[derive(Clone, Copy)]
pub struct Subst<E: Prop, A: Prop, B: Prop>(E, A, B);

/// `a[a := b] == b`
pub fn subst_trivial<A: Prop, B: Prop>() -> Eq<Subst<A, A, B>, B> {unimplemented!()}
/// `a[b := a] == a`.
pub fn subst_id<A: Prop, B: Prop>() -> Eq<Subst<A, B, A>, A> {unimplemented!()}
/// `(a : b) => (b[c := a] == b)`.
pub fn subst_ty<A: Prop, B: Prop, C: Prop>(_ty_a: Ty<A, B>) -> Eq<Subst<B, C, A>, B> {
    unimplemented!()
}
/// `is_const(a) => (a[b := c] == d)`.
pub fn subst_const<A: Prop, B: Prop, C: Prop>(_a_is_const: IsConst<A>) -> Eq<Subst<A, B, C>, A> {
    unimplemented!()
}
/// `(a, b)[c := d] == (a[c := d], b[c := d])`.
pub fn subst_tup<A: Prop, B: Prop, C: Prop, D: Prop>() ->
    Eq<Subst<Tup<A, B>, C, D>, Tup<Subst<A, C, D>, Subst<B, C, D>>> {unimplemented!()}
/// `(\(a : x) = b)[a := c] == b[a := c]`.
pub fn subst_lam<A: Prop, B: Prop, C: Prop, D: Prop, X: Prop>() ->
    Eq<Subst<Lam<Ty<A, X>, B>, C, D>, Lam<Ty<A, Subst<X, C, D>>, Subst<Subst<B, C, D>, A, C>>>
{unimplemented!()}
/// `(\(a : x) = b)[a := c] == b[a := c]`.
pub fn subst_lam_const<A: Prop, B: Prop, C: Prop, D: Prop, X: Prop>(
    _x: Eq<Subst<Lam<Ty<A, X>, B>, C, D>, Lam<Ty<A, Subst<X, C, D>>, Subst<Subst<B, C, D>, A, C>>>
) -> IsConst<A> {unimplemented!()}
/// `a[c := d] == b  =>  a[c := d][e := f] == b[e := f]`.
pub fn subst_eq<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop, F: Prop>(_x: Eq<Subst<A, C, D>, B>) ->
    Eq<Subst<Subst<A, C, D>, E, F>, Subst<B, C, D>> {unimplemented!()}
/// `a[c := d] == b  =>  (\(e) = a[c := d]) == (\(e) = b)`.
pub fn subst_eq_lam_body<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
    _x: Eq<Subst<A, C, D>, B>
) -> Eq<Lam<E, Subst<A, C, D>>, Lam<E, B>> {unimplemented!()}

/// Whether some symbol is a constant.
#[derive(Copy, Clone)]
pub struct IsConst<A>(A);

/// `is_const(a) ⋀ is_const(b)  =>  is_const((a, b))`.
pub fn const_tup<A: Prop, B: Prop>(a: IsConst<A>, b: IsConst<B>) -> IsConst<Tup<A, B>> {
    tup_is_const(a, b)
}
/// `is_const((a, b))  =>  is_const(a) ⋀ is_const(b)`.
pub fn tup_const<A: Prop, B: Prop>(_x: IsConst<Tup<A, B>>) -> And<IsConst<A>, IsConst<B>> {
    unimplemented!()
}

/// Lambda.
#[derive(Copy, Clone)]
pub struct Lam<X, Y>(X, Y);

/// `(a : x) ⋀ (b : y)  =>  (\(a : x) = b) : (x => y)`.
pub fn lam_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _ty_a: Ty<A, X>,
    _ty_b: Ty<B, Y>,
) -> Ty<Lam<Ty<A, X>, B>, Imply<X, Y>> {unimplemented!()}
/// `(a : x) ⋀ b  =>  (\(a : x) = b)`.
pub fn lam_lift<A: Prop, B: Prop, X: Prop>(ty_a: Ty<A, X>, b: B) -> Lam<Ty<A, X>, B> {Lam(ty_a, b)}
/// `(c : x) => ((\(a : x) = b)(c) == b[a := c])`.
pub fn lam<A: Prop, B: Prop, X: Prop, C: Prop>(
    _ty_c: Ty<C, X>
) -> Eq<App<Lam<Ty<A, X>, B>, C>, Subst<B, A, C>> {unimplemented!()}

/// `(a : x) ⋀ (b : y) ⋀ (c : x) ⋀ is_const(x)  =>  ((\(a : x) = b)(c) : y)`.
pub fn lam_app_ty<A: Prop, B: Prop, X: Prop, Y: Prop, C: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
    ty_c: Ty<C, X>,
    x_is_const: IsConst<X>
) -> Ty<App<Lam<Ty<A, X>, B>, C>, Y> {
    let ty_lam: Ty<Lam<Ty<A, X>, B>, Imply<X, Y>> = lam_ty(ty_a, ty_b);
    let app_lam_ty: Ty<App<_, _>, Y> = app_lam_ty(ty_lam, ty_c, x_is_const);
    app_lam_ty
}
/// `(a : x) ⋀ (b : y) ⋀ (c : x)  =>  ((\(a : x) = b)(c) : y[a := c])`.
pub fn lam_dep_app_ty<A: Prop, B: Prop, X: Prop, Y: Prop, C: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
    ty_c: Ty<C, X>,
) -> Ty<App<Lam<Ty<A, X>, B>, C>, Subst<Y, A, C>> {
    let ty_lam: Ty<Lam<Ty<A, X>, B>, Imply<X, Y>> = lam_ty(ty_a.clone(), ty_b.clone());
    let app_lam_ty: Ty<App<_, _>, Subst<Y, A, C>> = app_dep_lam_ty(ty_lam, ty_a, ty_b, ty_c);
    app_lam_ty
}
/// `(a : x) ⋀ (b : x)  =>  (\(a : x) = b)(b) : x`.
pub fn lam_app_ty_trivial<A: Prop, B: Prop, X: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>,
) -> Ty<App<Lam<Ty<A, X>, B>, B>, X> {
    let y = lam_dep_app_ty(ty_a, ty_b.clone(), ty_b.clone());
    path_semantics::ty_in_right_arg(y, subst_ty(ty_b))
}
/// `(b : x) => ((\(a : x) = b)(b) == b`.
pub fn lam_app_trivial<A: Prop, B: Prop, X: Prop>(
    ty_b: Ty<B, X>
) -> Eq<App<Lam<Ty<A, X>, B>, B>, B> {
    eq::transitivity(lam(ty_b), subst_id())
}

/// `\(a : x) = a`.
pub type LamId<A, X> = Lam<Ty<A, X>, A>;

/// `(\(a : x) = a) ~~ id`.
pub fn lam_id_q<A: Prop, X: Prop>() -> Q<LamId<A, X>, FId> {unimplemented!()}

/// `(a : x)  =>  (\(a : x) = a) : (x => x)`.
pub fn lam_id_ty<A: Prop, X: Prop>(ty_a: Ty<A, X>) -> Ty<LamId<A, X>, Imply<X, X>> {
    lam_ty(ty_a.clone(), ty_a)
}
/// `(a : x) ⋀ (b : x)  =>  (\(a : x) = a)(b) : x`.
pub fn lam_id_app_ty<A: Prop, B: Prop, X: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>,
    x_is_const: IsConst<X>
) -> Ty<App<LamId<A, X>, B>, X> {
    app_lam_ty(lam_id_ty(ty_a), ty_b, x_is_const)
}
/// `(\(a : x) = a)(b) = b`.
pub fn lam_id<A: Prop, B: Prop, X: Prop>() -> Eq<App<LamId<A, X>, B>, B> {
    eq::transitivity(app_map_eq(quality::to_eq(lam_id_q())), id_def())
}

/// `\(a : x) = \(b : y) = a`.
pub type LamFst<A, X, B, Y> = Lam<Ty<A, X>, Lam<Ty<B, Y>, A>>;

/// `(a : x) ⋀ (b : y)  =>  (\(a : x) = \(b : y) = a) : x`
pub fn lam_fst_ty<A: Prop, X: Prop, B: Prop, Y: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
) -> Ty<LamFst<A, X, B, Y>, Imply<X, Imply<Y, X>>> {
    lam_ty(ty_a.clone(), lam_ty(ty_b, ty_a))
}
/// `(c : x)  =>  (\(a : x) = \(b : y) = a)(c) == (\(b : y[a := c]) = c)`.
pub fn lam_fst<A: Prop, X: Prop, B: Prop, Y: Prop, C: Prop>(
    ty_c: Ty<C, X>
) -> Eq<App<LamFst<A, X, B, Y>, C>, Lam<Ty<B, Subst<Y, A, C>>, C>> {
    eq::transitivity(eq::transitivity(lam(ty_c.clone()), subst_lam()),
        subst_eq_lam_body(eq::transitivity(subst_eq(subst_trivial()), subst_id())))
}

/// `\(a : x) = \(b : y) = b`.
pub type LamSnd<A, X, B, Y> = Lam<Ty<A, X>, LamId<B, Y>>;

/// `(a : x) ⋀ (b : y)  =>  (\(a : x) = \(b : y) = b) : y`.
pub fn lam_snd_ty<A: Prop, X: Prop, B: Prop, Y: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>
) -> Ty<LamSnd<A, X, B, Y>, Imply<X, Imply<Y, Y>>> {
    lam_ty(ty_a, lam_ty(ty_b.clone(), ty_b))
}
/// `(c : x)  =>  (\(a : x) = \(b : y) = b)(c) == (\(b : y[a := c]) = b)`.
pub fn lam_snd<A: Prop, B: Prop, C: Prop, X: Prop, Y: Prop>(
    ty_c: Ty<C, X>
) -> Eq<App<LamSnd<A, X, B, Y>, C>, Lam<Ty<B, Subst<Y, A, C>>, B>> {
    let x2 = subst_lam();
    let b_is_const = subst_lam_const(x2.clone());
    eq::transitivity(lam(ty_c), eq::transitivity(x2,
        subst_eq_lam_body(eq::transitivity(subst_eq(subst_const(b_is_const.clone())),
            subst_const(b_is_const)))))
}

/// Dependent function type `(a : x) -> p(a)`.
pub type DepFunTy<A, X, PredP> = Pow<App<PredP, A>, Ty<A, X>>;
/// Dependent function `f : ((a : x) -> p(a))`.
pub type DepFun<F, A, X, PredP> = Ty<F, DepFunTy<A, X, PredP>>;
/// Dependent lambda type `(a : x) => p(a)`.
pub type DepLamTy<A, X, PredP> = Imply<Ty<A, X>, App<PredP, X>>;
/// Dependent lambda `f : ((a : x) => p(a))`.
pub type DepLam<F, A, X, PredP> = Ty<F, DepLamTy<A, X, PredP>>;

/// Parallel tuple.
#[derive(Copy, Clone)]
pub struct ParTup(());

/// `(f : (x1 -> y1)) ⋀ (g : (x2 -> y2))  =>  (f x g) : ((x1, x2) -> (y1, y2))`.
pub fn par_tup_fun_ty<F: Prop, G: Prop, X1: Prop, X2: Prop, Y1: Prop, Y2: Prop>(
    _ty_f: Ty<F, Pow<Y1, X1>>,
    _ty_g: Ty<G, Pow<Y2, X2>>,
) -> Ty<App<ParTup, Tup<F, G>>, Pow<Tup<Y1, Y2>, Tup<X1, X2>>> {
    unimplemented!()
}
/// `(f : (x1 => y1)) ⋀ (g : (x2 => y2))  =>  (f x g) : ((x1, x2) => (y1, y2))`.
pub fn par_tup_lam_ty<F: Prop, G: Prop, X1: Prop, X2: Prop, Y1: Prop, Y2: Prop>(
    _ty_f: Ty<F, Imply<X1, Y1>>,
    _ty_g: Ty<G, Imply<X2, Y2>>,
) -> Ty<App<ParTup, Tup<F, G>>, Imply<Tup<X1, X2>, Tup<Y1, Y2>>> {
    unimplemented!()
}
/// `is_const(par_tup)`.
pub fn par_tup_is_const() -> IsConst<ParTup> {unimplemented!()}
/// `is_const(f) ⋀ is_const(g)  =>  is_const(f x g)`.
pub fn par_tup_app_is_const<F: Prop, G: Prop>(
    f: IsConst<F>,
    g: IsConst<G>
) -> IsConst<App<ParTup, Tup<F, G>>> {
    app_is_const(par_tup_is_const(), tup_is_const(f, g))
}

/// `(f(i0) == o0) ⋀ (g(i1) == o1)  =>  (f x g)(i0, i1) == (o0, o1)`.
pub fn par_tup_def<F: Prop, G: Prop, I0: Prop, I1: Prop, O0: Prop, O1: Prop>(
    _eq0: Eq<App<F, I0>, O0>,
    _eq1: Eq<App<G, I1>, O1>,
) -> Eq<App<App<ParTup, Tup<F, G>>, Tup<I0, I1>>, Tup<O0, O1>> {unimplemented!()}

/// `f[g1 -> g2]`.
///
/// Normal path of 1 argument.
pub type Norm1<F, G1, G2> = Comp<Comp<G2, F>, Inv<G1>>;
/// `f[g]` of 1 argument.
pub type SymNorm1<F, G> = Norm1<F, G, G>;
/// `f[g1 x g2 -> g3]`.
///
/// Normal path of 2 arguments.
pub type Norm2<F, G1, G2, G3> = Comp<Comp<G3, F>, App<ParTup, Tup<Inv<G1>, Inv<G2>>>>;
/// `f[g]` of 2 arguments.
pub type SymNorm2<F, G> = Norm2<F, G, G, G>;
