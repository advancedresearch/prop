//! # Homotopy Type Theory
//!
//! *Notice! This module is experimental and in early stages of development.*
//!
//! This is a model of Homotopy Type Theory that attempts to be similar to the version in
//! the [standard HoTT book](https://homotopytypetheory.org/book/).

use crate::*;
use fun::App;
use hooo::Pow;
use path_semantics::Ty;
use nat::{Nat, S, Z};

/// Whether some type is a homotopy proposition.
#[derive(Copy, Clone)]
pub struct IsHType<N: Nat, A: Prop>(N, A);

/// Identity type.
#[derive(Copy, Clone)]
pub struct Id<T: Prop, PathP: Prop, PathQ: Prop>(T, PathP, PathQ);

/// Reflexivity proof of identity type.
#[derive(Copy, Clone)]
pub struct Refl<X: Prop, A: Prop>(X, A);

/// Whether some type is a homotopy proposition of level 0.
pub type IsContr<A> = IsHType<Z, A>;
/// Whether some type is a homotopy proposition of level 1.
pub type IsProp<A> = IsHType<S<Z>, A>;
/// Whether some type is a homotopy proposition of level 2.
pub type IsSet<A> = IsHType<S<S<Z>>, A>;
/// Whether some type is a homotopy n-groupoid.
pub type IsNGroupoid<N, A> = IsHType<S<S<N>>, A>;
/// Whether some type is a groupoid.
pub type IsGroupoid<A> = IsNGroupoid<S<Z>, A>;

/// `(a : x)  =>  refl{x}(a) : id{x}(a, a)`.
pub fn refl<A: Prop, X: Prop, PathP: Prop>(_ty_a: Ty<A, X>) -> Ty<Refl<X, A>, Id<X, A, A>>{
    unimplemented!()
}
/// `id{x}(a, b) => (a == b)`.
pub fn id_to_eq<A: Prop, B: Prop, X: Prop>(_: Id<X, A, B>) -> Eq<A, B> {unimplemented!()}
/// `(id{x}(a, b) ⋀ id{x}(a, c)) => id{x}(c, b)`.
pub fn id_in_left_arg<A: Prop, B: Prop, C: Prop, X: Prop>(
    p: Id<X, A, B>,
    q: Id<X, A, C>
) -> Id<X, C, B> {Id(p.0, q.2, p.2)}
/// `(id{x}(a, b) ⋀ id{x}(b, c)) => id{x}(a, b)`.
pub fn id_in_right_arg<A: Prop, B: Prop, C: Prop, X: Prop>(
    p: Id<X, A, B>,
    q: Id<X, B, C>
) -> Id<X, A, C> {Id(p.0, p.1, q.2)}
/// `(f : x -> y) ⋀ id{x}(a, b) => id{y}(f(a), f(b))`.
pub fn ap_fun<F: Prop, X: Prop, Y: Prop, A: Prop, B: Prop>(
    _f: Ty<F, Pow<Y, X>>,
    _p: Id<X, A, B>,
) -> Id<Y, App<F, A>, App<F, B>> {unimplemented!()}
/// `(f : x => y) ⋀ id{x}(a, b) => id{y}(f(a), f(b))`.
pub fn ap_lam<F: Prop, X: Prop, Y: Prop, A: Prop, B: Prop>(
    _f: Ty<F, Imply<X, Y>>,
    _p: Id<X, A, B>,
) -> Id<Y, App<F, A>, App<F, B>> {unimplemented!()}
/// `is_contr(a) => a`.
pub fn from_is_contr<A: Prop>(x: IsContr<A>) -> A {x.1}
/// `a => is_contr(a)`.
pub fn to_is_contr<A: Prop>(x: A) -> IsContr<A> {IsHType(Z, x)}
/// `(is_htype(n+1, x) ⋀ (a : x) ⋀ (b : x)) => is_htype(n, id{x}(a, b))`.
pub fn is_htype_to_id<A: Prop, B: Prop, X: Prop, N: Nat>(
    _: IsHType<S<N>, X>,
    _: Ty<A, X>,
    _: Ty<B, X>
) -> IsHType<N, Id<X, A, B>> {unimplemented!()}
/// `(is_prop(x) ⋀ (a : x) ⋀ (b : x)) => id{x}(a, b)`.
pub fn is_prop_to_id<A: Prop, B: Prop, X: Prop>(
    is_prop: IsProp<X>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>
) -> Id<X, A, B> {
    from_is_contr(is_htype_to_id(is_prop, ty_a, ty_b))
}
/// `(is_set(x) ⋀ (a : x) ⋀ (b : x)) => is_prop(id{x}(a, b))`.
pub fn is_set_to_is_prop<A: Prop, B: Prop, X: Prop>(
    is_set: IsSet<X>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>
) -> IsProp<Id<X, A, B>> {
    is_htype_to_id(is_set, ty_a, ty_b)
}
/// `(is_groupoid(x) ⋀ (a : x) ⋀ (b : x)) => is_set(id{x}(a, b))`.
pub fn is_groupoid_to_is_set<A: Prop, B: Prop, X: Prop>(
    is_groupoid: IsGroupoid<X>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>
) -> IsSet<Id<X, A, B>> {
    is_htype_to_id(is_groupoid, ty_a, ty_b)
}
/// `(is_set(x) ⋀ (a : x) ⋀ (b : x) ⋀ (p : id{x}(a, b)) ⋀ (q : id{x}(a, b))) =>
/// id{id{x}(a, b)}(p, q)`.
pub fn is_set_to_id<A: Prop, B: Prop, X: Prop, PathP: Prop, PathQ: Prop>(
    is_set: IsSet<X>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>,
    path_p: Ty<PathP, Id<X, A, B>>,
    path_q: Ty<PathQ, Id<X, A, B>>
) -> Id<Id<X, A, B>, PathP, PathQ> {
    let is_prop_eq: IsProp<Id<X, A, B>> = is_set_to_is_prop(is_set, ty_a, ty_b);
    is_prop_to_id(is_prop_eq, path_p, path_q)
}
/// `(is_groupoid(x) ⋀ (a : x) ⋀ (b : x) ⋀ (p : id{x}(a, b)) ⋀
/// (q : id{x}(a, b)) ⋀ (hp : id{id{x}(a, b)}(p, q)) ⋀ (hq : id{id{x}(a, b)}(p, a))) =>
/// id{id{id{x}(a, b)}(p, q)}(hp, hq)`.
pub fn is_groupoid_to_id<
    A: Prop, B: Prop, X: Prop,
    PathP: Prop, PathQ: Prop, HomP: Prop, HomQ: Prop,
>(
    is_groupoid: IsGroupoid<X>,
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>,
    path_p: Ty<PathP, Id<X, A, B>>,
    path_q: Ty<PathQ, Id<X, A, B>>,
    hom_p: Ty<HomP, Id<Id<X, A, B>, PathP, PathQ>>,
    hom_q: Ty<HomQ, Id<Id<X, A, B>, PathP, PathQ>>
) -> Id<Id<Id<X, A, B>, PathP, PathQ>, HomP, HomQ> {
    let is_set_eq = is_groupoid_to_is_set(is_groupoid, ty_a, ty_b);
    let is_prop_eq = is_set_to_is_prop(is_set_eq, path_p, path_q);
    is_prop_to_id(is_prop_eq, hom_p, hom_q)
}
/// `is_contr(true)`.
pub fn true_is_contr() -> IsContr<True> {to_is_contr(True)}
