//! # Imaginary Inverse
//!
//! The syntax `~x` uses `Qu<X>` from the [qubit] module,
//! and the syntax `x ~~ y` uses `Q<X, Y>` from the [quality] module.
//!
//! This model uses [imaginary inverse](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/imaginary-inverse.pdf)
//! `inv(f)` with `~inv(f)` or `~f` as a proof of bijective inverse of `f`.
//! Here, `~` means the path semantical qubit operator, such that:
//!
//! ```text
//! (inv(f) ~~ g) => ~inv(f)
//! ```
//!
//! From `~inv(f)` one can prove `~f` and vice versa ([inv_qu] and [inv_rev_qu]).
//!
//! It means that one uses path semantical quality instead of equality for inverses.
//! Path semantical quality `inv(f) ~~ g` also implies `inv(f) == g`,
//! which is useful in proofs ([quality::to_eq]).
//!
//! The [inv_val_qu] axiom makes it possible to compute using the inverse:
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
//! If a function `f` has no inverse, then it is useful to prove `false^(inv(f) ~~ g)`.

use super::*;

/// Imaginary inverse.
#[derive(Copy, Clone)]
pub struct FInv(());

/// `is_const(inv)`.
pub fn finv_is_const() -> IsConst<FInv> {unimplemented!()}

/// `inv(f)`.
pub type Inv<F> = App<FInv, F>;

/// `injective(f, a, b) := (f(a) == f(b)) => (a == b)`.
pub type Injective<F, A, B> = Imply<Eq<App<F, A>, App<F, B>>, Eq<A, B>>;

/// `surjective(f, x, y, b, a) := (f : x -> y) ⋀ (b : y) => ∃ a : x { f(a) == b }`.
pub type Surjective<F, X, Y, B, A> = Imply<
    And<Ty<F, Pow<X, Y>>, Ty<B, Y>>,
    Exists<Ty<A, X>, Eq<App<F, A>, B>>
>;

/// Inverse type `(f : x -> y) => (inv(f) : y -> x)`.
pub fn inv_ty<F: Prop, X: Prop, Y: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>
) -> Ty<Inv<F>, Pow<X, Y>> {unimplemented!()}
/// `~inv(f) ⋀ (f(a) == b)  =>  (inv(f)(b) == a)`.
///
/// Get inverse application of `f` if there exists a proof `~inv(f)`.
pub fn inv_val_qu<F: Prop, A: Prop, B: Prop>(
    _: Qu<Inv<F>>,
    _: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {unimplemented!()}
/// `inv(inv(f)) => f`.
pub fn inv_involve<F: Prop>(_: Inv<Inv<F>>) -> F {unimplemented!()}
/// `f => inv(inv(f))`.
pub fn involve_inv<F: Prop>(_: F) -> Inv<Inv<F>> {unimplemented!()}
/// `(inv(f) == f)  =>  (inv(f) ~~ f)`.
pub fn self_inv_to_q<F: Prop>(_: Eq<Inv<F>, F>) -> Q<Inv<F>, F> {unimplemented!()}
/// `theory(f) ⋀ ~inv(f) ⋀ (f : x -> y) ⋀ (x -> y)  =>  f ⋀ inv(f)`.
///
/// This makes it possible to get inverse map for free.
pub fn path<F: Prop, X: Prop, Y: Prop>(
    _: Theory<F>,
    _: Qu<Inv<F>>,
    _: Ty<F, Pow<Y, X>>,
    _: Pow<Y, X>
) -> And<F, Inv<F>> {unimplemented!()}

/// `is_const(f) => is_const(inv(f))`.
pub fn inv_is_const<F: Prop>(a: IsConst<F>) -> IsConst<Inv<F>> {app_is_const(finv_is_const(), a)}
/// `(f ~~ g) ⋀ (f(a) == b)  =>  (inv(f)(b) == a)`.
///
/// Get inverse map of `f` if there exists a proof `g`.
///
/// The proof needs to be path semantical quality,
/// since equality is reflexive and this leads to contradiction
/// if values are mutually exclusive.
pub fn inv_val<F: Prop, G: Prop, A: Prop, B: Prop>(
    x: Q<Inv<F>, G>,
    y: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {inv_val_qu(Qu::<Inv<F>>::from_q(quality::left(x)), y)}
/// `(inv(f) ~~ g) ⋀ (f(a) == b)  =>  (g(b) == a)`.
///
/// Get inverse map of `f` by `g`.
pub fn inv_val_other<F: Prop, G: Prop, A: Prop, B: Prop>(
    x: Q<Inv<F>, G>,
    y: Eq<App<F, A>, B>
) -> Eq<App<G, B>, A> {eq::in_left_arg(inv_val(x.clone(), y), app_map_eq(quality::to_eq(x)))}
/// `inv(inv(f)) == f`.
pub fn involve_eq<F: Prop>() -> Eq<Inv<Inv<F>>, F> {
    hooo::pow_eq_to_tauto_eq((inv_involve, involve_inv))(True)
}
/// `theory(f) ⋀ ~inv(f) ⋀ (f : x -> y) ⋀ (x -> y)  =>  (y -> x)`.
pub fn path_inv<F: Prop, X: Prop, Y: Prop>(
    theory_f: Theory<F>,
    qu_inv_f: Qu<Inv<F>>,
    ty_f: Ty<F, Pow<Y, X>>,
    x: Pow<Y, X>
) -> Pow<X, Y> {ty::ty_true(ty::triv(inv_ty(ty_f.clone()), path(theory_f, qu_inv_f, ty_f, x).1))}
/// `~f ⋀ (f == g)^true  =>  f ~~ g`.
pub fn qu_tauto_eq_to_q<F: Prop, G: Prop>(x: Qu<F>, tauto_eq: Tauto<Eq<F, G>>) -> Q<F, G> {
    (tauto_eq(True), (x.clone(), hooo::qu_in_arg(x, tauto_eq)))
}
/// `~f => ~inv(inv(f))`.
pub fn qu_double<F: Prop>(x: Qu<F>) -> Qu<Inv<Inv<F>>> {
    qu_tauto_eq_to_q(x, hooo::pow_eq_to_tauto_eq((involve_inv, inv_involve))).1.1
}
/// `~inv(inv(f)) => ~f`.
pub fn qu_rev_double<F: Prop>(x: Qu<Inv<Inv<F>>>) -> Qu<F> {
    qu_tauto_eq_to_q(x, hooo::pow_eq_to_tauto_eq((inv_involve, involve_inv))).1.1
}
/// `~f  ==  ~inv(inv(f))`.
pub fn eq_qu_double<F: Prop>() -> Eq<Qu<F>, Qu<Inv<Inv<F>>>> {
    (Rc::new(qu_double), Rc::new(qu_rev_double))
}
/// `(f == g)  =>  inv(f) == inv(g)`.
pub fn inv_eq<F: Prop, G: Prop>(x: Eq<F, G>) -> Eq<Inv<F>, Inv<G>> {app_eq(x)}
/// `~inv(f) ⋀ (f == g)^true  =>  ~inv(g)`.
pub fn qu_inv_tauto_eq_to_qu_inv<F: Prop, G: Prop>(
    x: Qu<Inv<F>>,
    tauto_eq: Tauto<Eq<F, G>>
) -> Qu<Inv<G>> {qu_tauto_eq_to_q(x, hooo::pow_transitivity(tauto_eq, inv_eq)).1.1}
/// `inv(inv(f))(x) == f(x)`.
pub fn inv_double_val<F: Prop, X: Prop>() -> Eq<App<Inv<Inv<F>>, X>, App<F, X>> {
    app_map_eq(involve_eq())
}
/// `~f ⋀ ~inv(f)  =>  (f(a) == b) == (inv(f)(b) == a)`.
pub fn qu_to_app_eq<A: Prop, B: Prop, F: Prop>(
    qu_f: Qu<F>, qu_inv_f: Qu<Inv<F>>
) -> Eq<Eq<App<F, A>, B>, Eq<App<Inv<F>, B>, A>> {
    (Rc::new(move |y| inv_val_qu(qu_inv_f.clone(), y)),
     Rc::new(move |y|
        eq::in_left_arg(inv_val_qu(qu_double(qu_f.clone()), y), app_map_eq(involve_eq()))))
}
/// `inv(f) == g  =>  inv(g) == f`.
pub fn inv_swap_eq<F: Prop, G: Prop>(x: Eq<Inv<F>, G>) -> Eq<Inv<G>, F> {
    eq::symmetry(eq::in_left_arg(inv_eq(x), involve_eq()))
}
/// `inv(f) == inv(g)  =>  f == g`.
pub fn inv_rev_eq<F: Prop, G: Prop>(x: Eq<Inv<F>, Inv<G>>) -> Eq<F, G> {
    eq::in_right_arg(eq::in_left_arg(inv_eq(x), involve_eq()), involve_eq())
}
