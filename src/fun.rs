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
use path_semantics::Ty;
use quality::Q;
use qubit::Qu;
use hooo::Pow;
use nat::{Nat, S, Z};

pub mod bool_alg;

/// Apply 2 function arguments.
pub type App2<F, X, Y> = App<App<F, X>, Y>;

/// Applied function.
#[derive(Clone)]
pub struct App<F: Prop, X: Prop>(F, X);

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
) -> Ty<App<F, A>, Y> {
    unimplemented!()
}

/// Get type of applied binary operator.
pub fn app2_fun_ty<F: Prop, X: Prop, Y: Prop, Z: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<Pow<Z, Y>, X>>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>
) -> Ty<App2<F, A, B>, Z> {
    app_fun_ty(app_fun_ty(ty_f, ty_a), ty_b)
}

/// Imaginary inverse.
#[derive(Clone)]
pub struct Inv<F: Prop>(F);

/// Inverse type `(f : x -> y) => (inv(f) : y -> x)`.
pub fn inv_ty<F: Prop, X: Prop, Y: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>
) -> Ty<Inv<F>, Pow<X, Y>> {unimplemented!()}

/// Get inverse map of `f` if there exists a proof `~inv(f)`.
pub fn inv_val_qu<F: Prop, A: Prop, B: Prop>(
    _: Qu<Inv<F>>,
    _: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {unimplemented!()}

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

/// `(g . f) ⋀ (g == h) => (h . f)`.
pub fn comp_in_left_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<G, H>) -> Comp<H, F> {
    Comp(y.0(x.0), x.1)
}

/// `(g . f) ⋀ (f == h) => (g . h)`.
pub fn comp_in_right_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<F, H>) -> Comp<G, H> {
    Comp(x.0, y.0(x.1))
}

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<FId, Pow<A, A>> {unimplemented!()}

/// Definition of identity function.
pub fn id_def<A: Prop>() -> Eq<App<FId, A>, A> {
    unimplemented!()
}

/// `inv(id) ~~ id`.
pub fn id_q() -> Q<Inv<FId>, FId> {unimplemented!()}

/// `(f . inv(f)) => id`.
pub fn comp_right_inv_to_id<F: Prop>(_: Comp<F, Inv<F>>) -> FId {
    unimplemented!()
}

/// `(inv(f) . f) => id`.
pub fn comp_left_inv_to_id<F: Prop>(_: Comp<Inv<F>, F>) -> FId {
    unimplemented!()
}

/// `(f : A -> B) => ((f ~~ inv(f)) : ((A -> B) ~~ (B -> A)))`.
pub fn self_inv_ty<F: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>
) -> Ty<Q<F, Inv<F>>, Q<Pow<B, A>, Pow<A, B>>> {
    path_semantics::ty_q_formation(ty_f.clone(), inv_ty(ty_f))
}

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

/// Cumulative type hierarchy.
pub struct Type<N: Nat>(N);

/// `type(n) : type(n+1)`.
pub fn type_ty<N: Nat>() -> Ty<Type<N>, Type<S<N>>> {unimplemented!()}

/// `(a -> b) : type(0)`.
pub fn pow_ty<A: Prop, B: Prop>() -> Ty<Pow<B, A>, Type<Z>> {unimplemented!()}
