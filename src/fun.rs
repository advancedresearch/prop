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
//! `inv(f)` with `~inv(f)` or `~f` as a proof of bijective inverse of `f`.
//! Here, `~` means the path semantical qubit operator, such that:
//!
//! ```text
//! (inv(f) ~~ g) => ~inv(f)
//! ```
//!
//! From `~inv(f)` one can prove `~f` and vice versa (`inv_qu` and `inv_rev_qu`).
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
//!
//! ### Function Extensionality
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
//!
//! ### Dependent Types
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
//!
//! ### Category Theory Perspective
//!
//! This model seen from a Category Theory perspective produces an ∞-groupoid.
//!
//! - Object: `A: Prop` as generic argument is an object `A` in the ∞-groupoid
//! - Morphism: `Ty<F, Pow<B, A>>` is a morphism `F` from `A` to `B`, `f : A -> B`
//! - Identity: `FId` is the identity morphism `id` from any object `A` to `A`
//! - Composition: `Comp<G, F>` is the composition `g . f`
//! - Inverse: `Inv<F>` is the imaginary inverse `inv(f)`
//!
//! The imaginary inverse adds an inverse for every morphism in the category,
//! which results in a groupoid. However, since the inverse is imaginary,
//! [the groupoid is category realizable](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/category-realizable-groupoids.pdf).
//!
//! Any expression constructed from these operations can be used where `A: Prop` is allowed.
//! Therefore, morphisms and higher morphisms are also objects, hence this form an ∞-groupoid.
//!
//! ### Qubit Truths
//!
//! The identity `id` (`FId`) has itself as an inverse `inv(id) ~~ id`.
//! From this, one can prove `~id`. Using `~id{A} : ~(A -> A)` it is possible to prove `~(A -> A)`.
//!
//! Now, it turns out that the proposition `A -> A`, or `A^A`, for any `A` is tautologically true.
//! Therefore, one can prove `~true` (`true_qu`) and as consequence:
//!
//! - `~true == true` (`eq_qu_true_true`)
//! - `~false == false` (`eq_qu_false_false`)
//!
//! This is amazing because it is a sophisticated result of Path Semantics using
//! PSI/PSQ/HOOO EP and Category Theory. One might expect that fundamental Path Semantics can
//! provide useful mathematical language design, but it is surprising that useful design can
//! provide insights/theorems into fundamental Path Semantics. The theorems above are not provable
//! using PSI/PSQ/HOOO EP alone.

use crate::*;
use path_semantics::{POrdProof, Ty};
use quality::Q;
use qubit::Qu;
use hooo::{Exists, Para, Pow, Tauto, Theory};
use hooo::pow::PowExt;
use nat::{Nat, S, Z};
use univalence::HomEq3;
pub use tup::*;

mod tup;

pub mod bool_alg;
pub mod hott;
pub mod real;
pub mod eqx;
pub mod fnat;
pub mod fin;
pub mod list;

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
/// `(f == g)  =>  (f(x) == f(y))`.
///
/// Lift equality of maps to application.
pub fn app_map_eq<F: Prop, G: Prop, X: Prop>(
    _eq_fg: Eq<F, G>
) -> Eq<App<F, X>, App<G, X>> {unimplemented!()}
/// `(f(a) : y)^(a : x)  =>  (f : (x -> y))`.
pub fn app_rev_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    _: Pow<Ty<App<F, A>, Y>, Ty<A, X>>
) -> Ty<F, Pow<Y, X>> {unimplemented!()}
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

/// `(f : (x -> y)) ⋀ (a : x)  =>  (f(a) : y)`.
///
/// Get type of applied function.
pub fn app_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    ty_f: Ty<F, Pow<Y, X>>,
    ty_a: Ty<A, X>,
) -> Ty<App<F, A>, Y> {app_lam_ty(fun_to_lam_ty(ty_f), ty_a)}
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
    lam_ty(ty_a, path_semantics::ty_in_left_arg(ty_b, eq::symmetry(x)))
}
/// `f : x -> y  =>  f : x => y`.
pub fn fun_to_lam_ty<F: Prop, X: Prop, Y: Prop>(ty_f: Ty<F, Pow<Y, X>>) -> Ty<F, Imply<X, Y>> {
    let x = hooo::pow_to_imply(hooo::pow_to_imply);
    (imply::transitivity(ty_f.0, x.clone()), ty_f.1.by_imply_right(x))
}
/// `(f(a)^a : x -> y)^true  =>  (f : x -> y)`.
pub fn app_fun_unfold<F: Prop, A: Prop, X: Prop, Y: Prop>(
    ty_f: Tauto<Ty<Pow<App<F, A>, A>, Pow<Y, X>>>,
) -> Ty<F, Pow<Y, X>> {app_rev_fun_ty(hooo::tauto_hooo_rev_ty(ty_f))}
/// `(f : x => y)^true  =>  (f^true : x -> y)`.
pub fn tauto_lam_to_tauto_fun_ty<F: Prop, X: Prop, Y: Prop>(
    ty_f: Tauto<Ty<F, Imply<X, Y>>>
) -> Ty<Tauto<F>, Pow<Y, X>> {
    use hooo::{tauto_imply_to_imply_tauto_pow, tauto_imply_to_pow, hooo_pord, pow_to_imply};

    (tauto_imply_to_imply_tauto_pow(ty_f.trans(and::fst)),
     hooo_pord(ty_f.trans(and::snd)).by_imply_right(pow_to_imply(tauto_imply_to_pow)))
}
/// `(f(a)^a : x => y)^true  =>  (f : x -> y)`.
pub fn app_tauto_lam_to_tauto_fun_ty<F: Prop, X: Prop, Y: Prop, A: Prop>(
    ty_f: Tauto<Ty<Pow<App<F, A>, A>, Imply<X, Y>>>
) -> Ty<F, Pow<Y, X>> {
    use hooo::pow_lift;

    let x = hooo::pow_tauto_to_pow_tauto_tauto(tauto_lam_to_tauto_fun_ty)(ty_f);
    let y = tauto!(path_semantics::ty_eq_left((Rc::new(|x: Tauto<_>| x(True)), Rc::new(pow_lift))));
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
/// `(f(a) : y)^true == (f(b) : y)^true`.
pub fn app_fun_swap_tauto_ty<F: Prop, Y: Prop, A: Prop, B: Prop>() ->
    Eq<Tauto<Ty<App<F, A>, Y>>, Tauto<Ty<App<F, B>, Y>>>
{
    use hooo::tr;
    use path_semantics::{ty_rev_true, ty_inhabit};

    let x: Tauto<True> = hooo::pow_refl;
    let ty_a = x.trans(ty_rev_true).trans(ty_inhabit);
    let ty_b = x.trans(ty_rev_true).trans(ty_inhabit);
    let (y1, y2) = (Rc::new(app_fun_swap_ty), Rc::new(app_fun_swap_ty));
    (Rc::new(move |x| ty_b.trans(y1(tr().trans(x)))),
     Rc::new(move |x| ty_a.trans(y2(tr().trans(x)))))
}

/// Imaginary inverse.
#[derive(Copy, Clone)]
pub struct Inv<F>(F);

/// Inverse type `(f : x -> y) => (inv(f) : y -> x)`.
pub fn inv_ty<F: Prop, X: Prop, Y: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>
) -> Ty<Inv<F>, Pow<X, Y>> {unimplemented!()}
/// `is_const(f) => is_const(inv(f))`.
pub fn inv_is_const<F: Prop>(_a: IsConst<F>) -> IsConst<Inv<F>> {unimplemented!()}
/// `~inv(f) ⋀ (f(a) == b)  =>  (inv(f)(b) == a)`.
///
/// Get inverse map of `f` if there exists a proof `~inv(f)`.
pub fn inv_val_qu<F: Prop, A: Prop, B: Prop>(
    _: Qu<Inv<F>>,
    _: Eq<App<F, A>, B>
) -> Eq<App<Inv<F>, B>, A> {unimplemented!()}
/// `inv(inv(f)) => f`.
pub fn inv_involve<F: Prop>(_: Inv<Inv<F>>) -> F {unimplemented!()}
/// `f => inv(inv(f))`.
pub fn involve_inv<F: Prop>(_: F) -> Inv<Inv<F>> {unimplemented!()}
/// `(f == g)  =>  inv(f) == inv(g)`.
pub fn inv_eq<F: Prop, G: Prop>(_: Eq<F, G>) -> Eq<Inv<F>, Inv<G>> {unimplemented!()}
/// `~f => ~inv(f)`.
pub fn inv_qu<F: Prop>(_: Qu<F>) -> Qu<Inv<F>> {unimplemented!()}
/// `theory(f) ⋀ ~inv(f) ⋀ (f : x -> y) ⋀ (x -> y)  =>  f ⋀ inv(f)`.
///
/// This makes it possible to get inverse map for free.
pub fn path<F: Prop, X: Prop, Y: Prop>(
    _: Theory<F>,
    _: Qu<Inv<F>>,
    _: Ty<F, Pow<Y, X>>,
    _: Pow<Y, X>
) -> And<F, Inv<F>> {unimplemented!()}

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
) -> Pow<X, Y> {
    use path_semantics::{ty_triv, ty_true};
    ty_true(ty_triv(inv_ty(ty_f.clone()), path(theory_f, qu_inv_f, ty_f, x).1))
}
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
/// `~inv(f) => ~f`.
pub fn inv_rev_qu<F: Prop>(x: Qu<Inv<F>>) -> Qu<F> {qu_rev_double(inv_qu(x))}
/// `~inv(f) ⋀ (f == g)^true  =>  ~inv(g)`.
pub fn qu_inv_tauto_eq_to_qu_inv<F: Prop, G: Prop>(
    x: Qu<Inv<F>>,
    tauto_eq: Tauto<Eq<F, G>>
) -> Qu<Inv<G>> {qu_tauto_eq_to_q(x, hooo::pow_transitivity(tauto_eq, inv_eq)).1.1}
/// `inv(inv(f))(x) == f(x)`.
pub fn inv_double_val<F: Prop, X: Prop>() -> Eq<App<Inv<Inv<F>>, X>, App<F, X>> {
    app_map_eq(involve_eq())
}
/// `f ~~ g  =>  inv(f) ~~ inv(g)`.
pub fn q_inv<F: Prop, G: Prop>((eq_fg, (qu_f, qu_g)): Q<F, G>) -> Q<Inv<F>, Inv<G>> {
    (inv_eq(eq_fg), (inv_qu(qu_f), inv_qu(qu_g)))
}
/// `inv(f) ~~ g  =>  f ~~ inv(g)`.
pub fn q_adjoint_left<F: Prop, G: Prop>(x: Q<Inv<F>, G>) -> Q<F, Inv<G>> {
    hooo::q_in_left_arg(q_inv(x), hooo::pow_eq_to_tauto_eq((inv_involve, involve_inv)))
}
/// `f ~~ inv(g)  =>  inv(f) ~~ g`.
pub fn q_adjoint_right<F: Prop, G: Prop>(x: Q<F, Inv<G>>) -> Q<Inv<F>, G> {
    quality::symmetry(q_adjoint_left(quality::symmetry(x)))
}
/// `inv(f) ~~ g  ==  f ~~ inv(g)`.
pub fn q_adjoint<F: Prop, G: Prop>() -> Eq<Q<Inv<F>, G>, Q<F, Inv<G>>> {
    hooo::pow_eq_to_tauto_eq((q_adjoint_left, q_adjoint_right))(True)
}
/// `~inv(f)  =>  (f(a) == b) == (inv(f)(b) == a)`.
pub fn qu_to_app_eq<A: Prop, B: Prop, F: Prop>(
    x: Qu<Inv<F>>
) -> Eq<Eq<App<F, A>, B>, Eq<App<Inv<F>, B>, A>> {
    let qu_inv_inv_f: Qu<Inv<Inv<F>>> = inv_qu(x.clone());

    (Rc::new(move |y| inv_val_qu(x.clone(), y)),
     Rc::new(move |y|
        eq::in_left_arg(inv_val_qu(qu_inv_inv_f.clone(), y), app_map_eq(involve_eq()))))
}

/// Composition.
#[derive(Copy, Clone)]
pub struct Comp<F, G>(F, G);

/// `(f : x -> y) ⋀ (g : y -> z)  =>  (g . f) : x -> z`.
///
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
/// `h . (g . f)  ==  (h . g) . f`.
pub fn comp_assoc<F: Prop, G: Prop, H: Prop>() -> Eq<Comp<H, Comp<G, F>>, Comp<Comp<H, G>, F>> {
    unimplemented!()
}
/// `id . f  ==  f`.
pub fn comp_id_left<F: Prop>() -> Eq<Comp<FId, F>, F> {unimplemented!()}
/// `f . id  ==  f`.
pub fn comp_id_right<F: Prop>() -> Eq<Comp<F, FId>, F> {unimplemented!()}
/// `~f ⋀ ~g  =>  ~(g . f)`.
pub fn comp_qu<F: Prop, G: Prop>(_: Qu<F>, _: Qu<G>) -> Qu<Comp<G, F>> {unimplemented!()}

/// `~inv(f) ⋀ ~inv(g)  =>  ~inv(g . f)`.
pub fn comp_inv_qu<F: Prop, G: Prop>(x: Qu<Inv<F>>, y: Qu<Inv<G>>) -> Qu<Inv<Comp<G, F>>> {
    inv_qu(comp_qu(inv_rev_qu(x), inv_rev_qu(y)))
}
/// `(inv(f) . inv(g)) == inv(g . f)`.
pub fn comp_inv<F: Prop, G: Prop>() -> Eq<Comp<Inv<F>, Inv<G>>, Inv<Comp<G, F>>> {
    (hooo::pow_to_imply(comp_inv_to_inv_comp), hooo::pow_to_imply(inv_comp_to_comp_inv))
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
/// `(f == h)  =>  (f . g) == (h . g)`.
pub fn comp_eq_left<F: Prop, G: Prop, H: Prop>(x: Eq<F, H>) -> Eq<Comp<F, G>, Comp<H, G>> {
    let x2 = eq::symmetry(x.clone());
    (Rc::new(move |fg| comp_in_left_arg(fg, x.clone())),
     Rc::new(move |hg| comp_in_left_arg(hg, x2.clone())))
}
/// `(g == h)  =>  (f . g) == (f . h)`.
pub fn comp_eq_right<F: Prop, G: Prop, H: Prop>(x: Eq<G, H>) -> Eq<Comp<F, G>, Comp<F, H>> {
    let x2 = eq::symmetry(x.clone());
    (Rc::new(move |fg| comp_in_right_arg(fg, x.clone())),
     Rc::new(move |fh| comp_in_right_arg(fh, x2.clone())))
}

/// Duplicate function.
#[derive(Clone, Copy)]
pub struct Dup(());

/// `dup : a -> (a, a)`.
///
/// Type of Dup.
pub fn dup_ty<A: Prop>() -> Ty<Dup, Pow<Tup<A, A>, A>> {unimplemented!()}
/// `is_const(dup)`.
pub fn dup_is_const() -> IsConst<Dup> {unimplemented!()}

/// `dup(a) = (a, a)`.
///
/// Definition of Dup function.
pub fn dup_def<A: Prop>() -> Eq<App<Dup, A>, Tup<A, A>> {unimplemented!()}

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// `id{a} : a -> a`.
///
/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<FId, Pow<A, A>> {unimplemented!()}
/// `is_const(id)`.
pub fn id_is_const() -> IsConst<FId> {unimplemented!()}

/// `(x : type(n)) ⋀ (a : x)  =>  id(a) = a`.
///
/// Definition of identity function.
pub fn id_def<A: Prop, X: Prop, N: Nat>(
    _ty_x: Ty<X, Type<N>>,
    _ty_a: Ty<A, X>
) -> Eq<App<FId, A>, A> {unimplemented!()}
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

/// `a : type(n)  =>  id(a) = a`.
pub fn id_def_type<A: Prop, N: Nat>(ty_a: Ty<A, Type<N>>) -> Eq<App<FId, A>, A> {
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
/// `(inv(f) == f) => ((f . f) == id)`.
pub fn self_inv_to_eq_id<F: Prop>(eq_f: Eq<Inv<F>, F>) -> Eq<Comp<F, F>, FId> {
    let eq_f_2 = eq_f.clone();
    (
        Rc::new(move |x| comp_right_inv_to_id(
            comp_in_right_arg(x, eq::symmetry(eq_f_2.clone())))),
        Rc::new(move |x| comp_in_right_arg(id_to_comp_right_inv(x), eq_f.clone())),
    )
}
/// `~id{a} : ~(a -> a)`.
pub fn id_qu_ty<A: Prop>() -> Ty<Qu<FId>, Qu<Pow<A, A>>> {path_semantics::ty_qu_formation(id_ty())}
/// `~id`.
pub fn id_qu() -> Qu<FId> {Qu::from_q(quality::right(id_q()))}
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
        tauto!((imply::id().map_any(), True.map_any()))))), |y| Qu::to_q(y))
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

/// `is_prop(a) := (~a == a)^true`.
pub type IsProp<A> = Tauto<Eq<Qu<A>, A>>;
/// `is_set(a) := is_prop(~a)`.
pub type IsSet<A> = IsProp<Qu<A>>;
/// `is_groupoid(a) := is_set(~a)`.
pub type IsGroupoid<A> = IsSet<Qu<A>>;

/// `is_prop(true)`.
pub fn is_prop_true() -> IsProp<True> {tauto!(eq_qu_true_true())}
/// `is_prop(false)`.
pub fn is_prop_false() -> IsProp<False> {tauto!(eq_qu_false_false())}
/// `a^b  =>  is_prop(a^b)`.
pub fn pow_to_is_prop<A: Prop, B: Prop>(x: Pow<A, B>) -> IsProp<Pow<A, B>> {
    x.lift().trans(pow_to_eq_qu)
}
/// `is_set(id)`.
pub fn is_set_id() -> IsSet<FId> {collapse_to_set_right(tauto!(id_q()))}
/// `is_set(not)`.
pub fn is_set_not() -> IsSet<bool_alg::FNot> {collapse_to_set_right(tauto!(bool_alg::not_q()))}
/// `is_prop(a)  =>  is_set(a)`.
pub fn is_prop_to_is_set<A: Prop>(x: IsProp<A>) -> IsSet<A> {
    fn f<A: Prop>(x: IsProp<A>) -> Eq<Qu<Qu<A>>, Qu<A>> {
        let x2 = hooo::tauto_eq_symmetry(x.clone());
        (Rc::new(move |y| qubit::in_arg(y, x)), Rc::new(move |y| qubit::in_arg(y, x2)))
    }
    x.lift().trans(f)
}
/// `is_set(a)  =>  is_groupoid(a)`.
pub fn is_set_to_is_groupoid<A: Prop>(x: IsSet<A>) -> IsGroupoid<A> {is_prop_to_is_set(x)}
/// `is_prop(a)  =>  is_groupoid(a)`.
pub fn is_prop_to_is_groupoid<A: Prop>(x: IsProp<A>) -> IsGroupoid<A> {
    is_set_to_is_groupoid(is_prop_to_is_set(x))
}
/// `a^true  =>  is_prop(a)`.
pub fn tauto_to_is_prop<A: Prop>(tauto_a: Tauto<A>) -> IsProp<A> {
    tauto_a.lift().trans(tauto_to_eq_qu)
}
/// `false^a  =>  is_prop(a)`.
pub fn para_to_is_prop<A: Prop>(para_a: Para<A>) -> IsProp<A> {para_a.lift().trans(para_to_eq_qu)}
/// `(f ~~ g)^true  =>  is_set(f)`.
pub fn collapse_to_set_left<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> IsSet<F> {
    x.trans(quality::left).trans(Qu::from_q).lift().trans(tauto_to_eq_qu)
}
/// `(f ~~ g)^true  =>  is_set(g)`.
pub fn collapse_to_set_right<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> IsSet<G> {
    collapse_to_set_left(x.trans(quality::symmetry))
}
/// `(f ~~ g)^true  =>  (~~g == ~~f)^true`.
pub fn collapse_to_eq_qu_2<F: Prop, G: Prop>(
    x: Tauto<Q<F, G>>
) -> Tauto<Eq<Qu<Qu<F>>, Qu<Qu<G>>>> {
    fn h<F: Prop, G: Prop>(q: Q<F, G>) -> Eq<Qu<F>, Qu<G>> {and::to_eq_pos(q.1)}
    hooo::tauto_eq_transitivity(
        hooo::tauto_eq_transitivity(collapse_to_set_left(x.clone()), x.trans(h)),
        hooo::tauto_eq_symmetry(collapse_to_set_right(x)))
}
/// `(f ~~ g)^true  =>  hom_eq(3, f, g)^true`.
pub fn collapse_to_hom_eq_3<F: Prop, G: Prop>(x: Tauto<Q<F, G>>) -> Tauto<HomEq3<F, G>> {
    use qubit::{Qubit, normalize, rev_normalize};
    use nat::Two;
    fn h<F: Prop, G: Prop>((a, b): Eq<Qu<Qu<F>>, Qu<Qu<G>>>) -> Eq<Qubit<Two, F>, Qubit<Two, G>> {
        (Rc::new(move |x| normalize(a(rev_normalize(x)))),
         Rc::new(move |x| normalize(b(rev_normalize(x)))))
    }
    hooo::hooo_rev_and((collapse_to_eq_qu_2(x).trans(h), x.trans(univalence::q_to_hom_eq_2)))
}

/// Cumulative type hierarchy.
#[derive(Copy, Clone)]
pub struct Type<N>(N);

impl<N: 'static + Clone> path_semantics::LProp for Type<N> {
    type N = N;
    type SetLevel<T: 'static + Clone> = Type<T>;
}

/// `type(n) => type(n+1)`.
pub fn type_imply<N: Nat>(Type(n): Type<N>) -> Type<S<N>> {Type(S(n))}
/// `is_const(type(n))`.
pub fn type_is_const<N: Nat>() -> IsConst<Type<N>> {unimplemented!()}
/// `(a : x) ⋀ (b : y)  =>  (a -> b) : (x -> y)`.
pub fn fun_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _: Ty<A, X>,
    _: Ty<B, Y>
) -> Ty<Pow<B, A>, Pow<Y, X>> {unimplemented!()}
/// `(type(n) -> type(m)) : type(0)`.
pub fn fun_type_ty<N: Nat, M: Nat>() -> Ty<Pow<Type<M>, Type<N>>, Type<Z>> {unimplemented!()}
/// `(b : type(n))  =>  (a : b) : type(n)`.
pub fn judgement_ty<A: Prop, B: Prop, N: Nat>(_ty_b: Ty<B, Type<N>>) -> Ty<Ty<A, B>, Type<N>> {
    unimplemented!()
}

/// `type(n) : type(n+1)`.
pub fn type_ty<N: Nat>() -> Ty<Type<N>, Type<S<N>>> {
    (hooo::pow_to_imply(type_imply), POrdProof::new())
}
/// `(a : type(n)) ⋀ (b : type(m))  =>  (a -> b) : type(0)`.
pub fn fun_type0<A: Prop, B: Prop, N: Nat, M: Nat>(
    ty_a: Ty<A, Type<N>>,
    ty_b: Ty<B, Type<M>>
) -> Ty<Pow<B, A>, Type<Z>> {path_semantics::ty_transitivity(fun_ty(ty_a, ty_b), fun_type_ty())}
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

/// `(a, b) : (x, y)  =>  (a : x)`.
pub fn tup_fst<A: Prop, B: Prop, X: Prop, Y: Prop>(
    ty_tup_ab: Ty<Tup<A, B>, Tup<X, Y>>
) -> Ty<A, X> {path_semantics::ty_in_left_arg(app_fun_ty(fst_ty(), ty_tup_ab), fst_def())}
/// `(a, b) : (x, y)  =>  (b : y)`.
pub fn tup_snd<A: Prop, B: Prop, X: Prop, Y: Prop>(
    ty_tup_ab: Ty<Tup<A, B>, Tup<X, Y>>
) -> Ty<B, Y> {path_semantics::ty_in_left_arg(app_fun_ty(snd_ty(), ty_tup_ab), snd_def())}
/// `(a, b) ⋀ (a == c)  =>  (c, b)`.
pub fn tup_in_left_arg<A: Prop, B: Prop, C: Prop>(x: Tup<A, B>, y: Eq<A, C>) -> Tup<C, B> {
    tup_eq_fst(y).0(x)
}
/// `(a, b) ⋀ (b == c)  =>  (a, c)`.
pub fn tup_in_right_arg<A: Prop, B: Prop, C: Prop>(x: Tup<A, B>, y: Eq<B, C>) -> Tup<A, C> {
    tup_eq_snd(y).0(x)
}
/// `(a, b)  ==  (fst((a, b)), snd((a, b)))`.
pub fn tup_eq_fst_snd<A: Prop, B: Prop>() ->
    Eq<Tup<A, B>, Tup<App<Fst, Tup<A, B>>, App<Snd, Tup<A, B>>>>
{eq::transitivity(eq::symmetry(tup_eq_fst(fst_def())), tup_eq_snd(eq::symmetry(snd_def())))}
/// `(a == b) ⋀ (c == d)  =>  (a, c) == (b, d)`.
pub fn tup_eq<A: Prop, B: Prop, C: Prop, D: Prop>(
    eq_ab: Eq<A, B>,
    eq_cd: Eq<C, D>
) -> Eq<Tup<A, C>, Tup<B, D>> {eq::transitivity(tup_eq_fst(eq_ab), tup_eq_snd(eq_cd))}

/// Tuple of 3 elements.
pub type Tup3<A, B, C> = Tup<A, Tup<B, C>>;

/// `(a, b, c) : (x, y, z)  =>  (a : x)`.
pub fn tup3_fst<A: Prop, B: Prop, C: Prop, X: Prop, Y: Prop, Z: Prop>(
    x: Ty<Tup3<A, B, C>, Tup3<X, Y, Z>>
) -> Ty<A, X> {tup_fst(x)}
/// `(a, b, c) : (x, y, z)  =>  (b : y)`.
pub fn tup3_snd<A: Prop, B: Prop, C: Prop, X: Prop, Y: Prop, Z: Prop>(
    x: Ty<Tup3<A, B, C>, Tup3<X, Y, Z>>
) -> Ty<B, Y> {tup_fst(tup_snd(x))}
/// `(a, b, c) : (x, y, z)  =>  (c : z)`.
pub fn tup3_trd<A: Prop, B: Prop, C: Prop, X: Prop, Y: Prop, Z: Prop>(
    x: Ty<Tup3<A, B, C>, Tup3<X, Y, Z>>
) -> Ty<C, Z> {tup_snd(tup_snd(x))}
/// `(a == b)  =>  (a, c, d) == (b, c, d)`.
pub fn tup3_eq_fst<A: Prop, B: Prop, C: Prop, D: Prop>(
    x: Eq<A, B>
) -> Eq<Tup3<A, C, D>, Tup3<B, C, D>> {tup_eq_fst(x)}
/// `(a == b)  =>  (c, a, d) == (c, b, d)`.
pub fn tup3_eq_snd<A: Prop, B: Prop, C: Prop, D: Prop>(
    x: Eq<A, B>
) -> Eq<Tup3<C, A, D>, Tup3<C, B, D>> {tup_eq_snd(tup_eq_fst(x))}
/// `(a == b)  =>  (c, d, a) == (c, d, b)`.
pub fn tup3_eq_trd<A: Prop, B: Prop, C: Prop, D: Prop>(
    x: Eq<A, B>
) -> Eq<Tup3<C, D, A>, Tup3<C, D, B>> {tup_eq_snd(tup_eq_snd(x))}
/// `(c : x) ⋀ (d : y) ⋀ ((a, c, d) == (b, c, d))  =>  (a == b)`.
pub fn tup3_rev_eq_fst<A: Prop, B: Prop, C: Prop, D: Prop, X: Prop, Y: Prop>(
    ty_c: Ty<C, X>,
    ty_d: Ty<D, Y>,
    x: Eq<Tup3<A, C, D>, Tup3<B, C, D>>
) -> Eq<A, B> {tup_rev_eq_fst(tup_ty(ty_c, ty_d), x)}
/// `(c : x) ⋀ (d : y) ⋀ ((c, a, d) == (c, b, d))  =>  (a == b)`.
pub fn tup3_rev_eq_snd<A: Prop, B: Prop, C: Prop, D: Prop, X: Prop, Y: Prop>(
    ty_c: Ty<C, X>,
    ty_d: Ty<D, Y>,
    x: Eq<Tup3<C, A, D>, Tup3<C, B, D>>
) -> Eq<A, B> {tup_rev_eq_fst(ty_d, tup_rev_eq_snd(ty_c, x))}
/// `(c : x) ⋀ (d : y) ⋀ ((c, d, a) == (c, d, b))  =>  (a == b)`.
pub fn tup3_rev_eq_trd<A: Prop, B: Prop, C: Prop, D: Prop, X: Prop, Y: Prop>(
    ty_c: Ty<C, X>,
    ty_d: Ty<D, Y>,
    x: Eq<Tup3<C, D, A>, Tup3<C, D, B>>
) -> Eq<A, B> {tup_rev_eq_snd(ty_d, tup_rev_eq_snd(ty_c, x))}

/// Fst.
#[derive(Copy, Clone)]
pub struct Fst(());

/// `fst : (a, b) -> a`.
///
/// Type of Fst.
pub fn fst_ty<A: Prop, B: Prop>() -> Ty<Fst, Pow<A, Tup<A, B>>> {unimplemented!()}
/// `is_const(fst)`.
pub fn fst_is_const() -> IsConst<Fst> {unimplemented!()}
/// `fst((a, b)) = a`.
pub fn fst_def<A: Prop, B: Prop>() -> Eq<App<Fst, Tup<A, B>>, A> {unimplemented!()}
/// `t : (x : a, b)  =>  fst(t) == x`.
pub fn fst_lower<T: Prop, X: Prop, A: Prop, B: Prop>(
    _: Ty<T, Tup<Ty<X, A>, B>>
) -> Eq<App<Fst, T>, X> {unimplemented!()}

/// `t : (a, b)  =>  fst(t) : a`.
pub fn fst<T: Prop, A: Prop, B: Prop>(x: Ty<T, Tup<A, B>>) -> Ty<App<Fst, T>, A> {
    app_fun_ty(fst_ty(), x)
}

/// Snd.
#[derive(Copy, Clone)]
pub struct Snd(());

/// `snd : (a, b) -> b`.
///
/// Type of Snd.
pub fn snd_ty<A: Prop, B: Prop>() -> Ty<Snd, Pow<B, Tup<A, B>>> {unimplemented!()}
/// `is_const(snd)`.
pub fn snd_is_const() -> IsConst<Snd> {unimplemented!()}
/// `snd((a, b)) = b`.
pub fn snd_def<A: Prop, B: Prop>() -> Eq<App<Snd, Tup<A, B>>, B> {unimplemented!()}
/// `t : (a, x : b)  =>  snd(t) == x`.
pub fn snd_lower<T: Prop, X: Prop, A: Prop, B: Prop>(
    _: Ty<T, Tup<A, Ty<X, B>>>
) -> Eq<App<Snd, T>, X> {unimplemented!()}

/// `t : (a, b)  =>  snd(t) : a`.
pub fn snd<T: Prop, A: Prop, B: Prop>(x: Ty<T, Tup<A, B>>) -> Ty<App<Snd, T>, B> {
    app_fun_ty(snd_ty(), x)
}

/// Substitute in expression `e[a := b]`.
///
/// Substitution is about replacing variables in an expression with constants or other variables.
/// Usually, the goal is to derive a constant expression that contains none variables.
#[derive(Clone, Copy)]
pub struct Subst<E, A, B>(E, A, B);

/// `a[a := b] == b`
pub fn subst_trivial<A: Prop, B: Prop>() -> Eq<Subst<A, A, B>, B> {unimplemented!()}
/// `a[b := b] == a`.
pub fn subst_nop<A: Prop, B: Prop>() -> Eq<Subst<A, B, B>, A> {unimplemented!()}
/// `(a : b) => (b[c := a] == b)`.
pub fn subst_ty<A: Prop, B: Prop, C: Prop>(_ty_a: Ty<A, B>) -> Eq<Subst<B, C, A>, B> {
    unimplemented!()
}
/// `is_const(a) => (a[b := c] == a)`.
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
/// `f(a)[b := c] == f[b := c](a[b := c])`.
pub fn subst_app<F: Prop, A: Prop, B: Prop, C: Prop>() ->
    Eq<Subst<App<F, A>, B, C>, App<Subst<F, B, C>, Subst<A, B, C>>> {unimplemented!()}

/// Whether some symbol is a constant.
///
/// When a symbol `x` is a constant, `x[a := b] == x` (invariant under substitution).
#[derive(Copy, Clone)]
pub struct IsConst<A>(A);

/// A proof that some symbol is not a constant.
///
/// This is used to prevent collapse of propositions into constants,
/// e.g. when doing a proof by induction.
pub type IsVar<A> = Not<IsConst<A>>;

/// Implemented by variable propositions.
pub trait VProp: Prop {
    /// Constructs a proof that the proposition is variable.
    fn is_var() -> IsVar<Self>;
}

/// `is_const(a) ⋀ is_const(b)  =>  is_const((a, b))`.
pub fn const_tup<A: Prop, B: Prop>(a: IsConst<A>, b: IsConst<B>) -> IsConst<Tup<A, B>> {
    tup_is_const(a, b)
}
/// `is_const((a, b))  =>  is_const(a) ⋀ is_const(b)`.
pub fn tup_const<A: Prop, B: Prop>(_x: IsConst<Tup<A, B>>) -> And<IsConst<A>, IsConst<B>> {
    unimplemented!()
}
/// `(a == b)  =>  (is_const(a) == is_const(b))`.
pub fn const_eq<A: Prop, B: Prop>((ab, ba): Eq<A, B>) -> Eq<IsConst<A>, IsConst<B>> {
    (Rc::new(move |a| IsConst(ab(a.0))), Rc::new(move |b| IsConst(ba(b.0))))
}

/// `is_const(a) ⋀ (a == b)  =>  is_const(b)`.
pub fn const_in_arg<A: Prop, B: Prop>(a: IsConst<A>, x: Eq<A, B>) -> IsConst<B> {
    const_eq(x).0(a)
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
/// `(a : x) ⋀ (b == c)  =>  (\(a : x) = b) == (\(a : x) = c)`.
pub fn lam_eq_lift<A: Prop, X: Prop, B: Prop, C: Prop>(
    _ty_a: Ty<A, X>,
    _eq: Eq<B, C>
) -> Eq<Lam<Ty<A, X>, B>, Lam<Ty<A, X>, C>> {unimplemented!()}
/// `(c : x) => ((\(a : x) = b)(c) == b[a := c])`.
pub fn lam<A: Prop, B: Prop, X: Prop, C: Prop>(
    _ty_c: Ty<C, X>
) -> Eq<App<Lam<Ty<A, X>, B>, C>, Subst<B, A, C>> {unimplemented!()}

/// `(a : x) ⋀ (b : y) ⋀ (c : x)  =>  ((\(a : x) = b)(c) : y)`.
pub fn lam_app_ty<A: Prop, B: Prop, X: Prop, Y: Prop, C: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, Y>,
    ty_c: Ty<C, X>,
) -> Ty<App<Lam<Ty<A, X>, B>, C>, Y> {
    let ty_lam: Ty<Lam<Ty<A, X>, B>, Imply<X, Y>> = lam_ty(ty_a, ty_b);
    let app_lam_ty: Ty<App<_, _>, Y> = app_lam_ty(ty_lam, ty_c);
    app_lam_ty
}
/// `(b : x)  =>  (\(a : x) = b)(b) : x`.
pub fn lam_app_ty_trivial<A: Prop, B: Prop, X: Prop>(
    ty_b: Ty<B, X>,
    b_is_const: IsConst<B>,
) -> Ty<App<Lam<Ty<A, X>, B>, B>, X> {
    path_semantics::ty_eq_left(lam_app_trivial(ty_b.clone(), b_is_const)).1(ty_b)
}
/// `(b : x) => ((\(a : x) = b)(b) == b`.
pub fn lam_app_trivial<A: Prop, B: Prop, X: Prop>(
    ty_b: Ty<B, X>,
    b_is_const: IsConst<B>
) -> Eq<App<Lam<Ty<A, X>, B>, B>, B> {
    eq::transitivity(lam(ty_b), subst_const(b_is_const))
}
/// `(a : x) => ((\(a : x) = b)(a) == b`.
pub fn lam_app_nop<A: Prop, B: Prop, X: Prop>(ty_a: Ty<A, X>) -> Eq<App<Lam<Ty<A, X>, B>, A>, B> {
    eq::transitivity(lam(ty_a), subst_nop())
}

/// `\(a : x) = a`.
pub type LamId<A, X> = Lam<Ty<A, X>, A>;

/// `(\(a : x) = a) == id`.
pub fn lam_id_eq<A: Prop, X: Prop>() -> Eq<LamId<A, X>, FId> {unimplemented!()}

/// `(\(a : x) = a) ~~ id`.
pub fn lam_id_q<A: Prop, X: Prop>() -> Q<LamId<A, X>, FId> {
    hooo::q_in_left_arg(quality::right(id_q()), hooo::tauto_eq_symmetry(tauto!(lam_id_eq())))
}
/// `(a : x)  =>  (\(a : x) = a) : (x => x)`.
pub fn lam_id_ty<A: Prop, X: Prop>(ty_a: Ty<A, X>) -> Ty<LamId<A, X>, Imply<X, X>> {
    lam_ty(ty_a.clone(), ty_a)
}
/// `(a : x) ⋀ (b : x)  =>  (\(a : x) = a)(b) : x`.
pub fn lam_id_app_ty<A: Prop, B: Prop, X: Prop>(
    ty_a: Ty<A, X>,
    ty_b: Ty<B, X>,
) -> Ty<App<LamId<A, X>, B>, X> {
    app_lam_ty(lam_id_ty(ty_a), ty_b)
}
/// `(x : type(n)) ⋀ (b : x)  =>  (\(a : x) = a)(b) = b`.
pub fn lam_id<A: Prop, B: Prop, X: Prop, N: Nat>(
    ty_x: Ty<X, Type<N>>,
    ty_b: Ty<B, X>
) -> Eq<App<LamId<A, X>, B>, B> {
    eq::transitivity(app_map_eq(quality::to_eq(lam_id_q())), id_def(ty_x, ty_b))
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
    ty_c: Ty<C, X>,
    c_is_const: IsConst<C>,
) -> Eq<App<LamFst<A, X, B, Y>, C>, Lam<Ty<B, Subst<Y, A, C>>, C>> {
    eq::transitivity(eq::transitivity(lam(ty_c), subst_lam()),
        subst_eq_lam_body(eq::transitivity(subst_eq(subst_trivial()), subst_const(c_is_const))))
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
    path_semantics::ty_in_right_arg(x, (Rc::new(dep_app), Rc::new(dep_app)))
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
        path_semantics::ty_transitivity(x, fun_type_ty())
    }
    hooo_rev_and((ty_x.trans(judgement_ty), pow_lift(pow_ty_pa_ty_a))).trans(f).trans(g)
}
/// `((a : x) -> (p(a) : y(a)))  =>  ((a -> p(a)) : ((b : x) -> y(b)))^true`.
pub fn dep_fun_intro<A: Prop, B: Prop, X: Prop, Y: Prop, P: Prop>(
    x: Pow<Ty<App<P, A>, App<Y, A>>, Ty<A, X>>
) -> Tauto<DepFun<Pow<App<P, A>, A>, A, X, Y>> {
    use hooo::{pow_transitivity, tauto_hooo_ty};

    tauto_hooo_ty(pow_transitivity(path_semantics::ty_lower, x.clone())).trans(dep_fun_swap_app_ty)
}
/// `(f : (a : x) -> p(a))^true ⋀ (b : x)^true  =>  (f(b) : p(b))^true`
pub fn dep_fun_elim<F: Prop, X: Prop, P: Prop, A: Prop, B: Prop>(
    ty_f: Tauto<DepFun<F, A, X, P>>,
    ty_b: Tauto<Ty<B, X>>
) -> Tauto<Ty<App<F, B>, App<P, B>>> {
    use hooo::hooo_rev_and;

    fn g<F: Prop, A: Prop, X: Prop, Y: Prop>(
        (f, x): And<Ty<F, Pow<Y, Ty<A, X>>>, Ty<A, X>>
    ) -> Ty<App<F, A>, Y> {app_fun_ty(f, path_semantics::ty_lift(x))}
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
        path_semantics::ty_transitivity(x, tup_type_ty())
    }
    hooo_rev_and((ty_x.trans(judgement_ty), pow_lift(pow_ty_pa_ty_a))).trans(f).trans(g)
}
/// `(a : x)^true ⋀ (b : p(a))^true  =>  ((a, b) : ((a : x, p(a))))^true`.
pub fn dep_tup_intro<A: Prop, X: Prop, B: Prop, P: Prop>(
    ty_a: Tauto<Ty<A, X>>,
    ty_b: Tauto<Ty<B, App<P, A>>>,
) -> Tauto<DepTup<A, X, B, P>> {
    let f = hooo::hooo_imply(tauto!(Rc::new(move |(ty_a, ty_b)| tup_ty(ty_a, ty_b))));
    let x = hooo::hooo_rev_and((ty_a.trans(path_semantics::ty_lift), ty_b));
    f(x)
}
/// `(t : (x : a, b(x)))^true  =>  (fst(t) : a)^true ⋀ (snd(t) : b(fst(t)))^true`.
pub fn dep_tup_elim<T: Prop, X: Prop, A: Prop, B: Prop>(
    ty_t: Tauto<Ty<T, Tup<Ty<X, A>, App<B, X>>>>
) -> And<Tauto<Ty<App<Fst, T>, A>>, Tauto<Ty<App<Snd, T>, App<B, App<Fst, T>>>>> {
    use hooo::{tauto_eq_symmetry, tauto_in_arg};
    use path_semantics::{ty_eq_left, ty_eq_right, ty_lower};

    let x = ty_t.trans(fst_lower);
    (tauto_in_arg(ty_t.trans(fst), tauto_eq_symmetry(x.trans(ty_eq_left)
        .trans(ty_eq_right))).trans(ty_lower),
     tauto_in_arg(ty_t.trans(snd), tauto_eq_symmetry(x.trans(app_eq).trans(ty_eq_right))))
}

/// Parallel tuple.
#[derive(Copy, Clone)]
pub struct ParTup(());

/// Apply parallel tuple to two functions.
pub type Par<F, G> = App<ParTup, Tup<F, G>>;

/// Apply parallel tuple to two inverted functions.
pub type ParInv<F, G> = Par<Inv<F>, Inv<G>>;

/// `(f : (x1 -> y1)) ⋀ (g : (x2 -> y2))  =>  (f x g) : ((x1, x2) -> (y1, y2))`.
pub fn par_tup_fun_ty<F: Prop, G: Prop, X1: Prop, X2: Prop, Y1: Prop, Y2: Prop>(
    _ty_f: Ty<F, Pow<Y1, X1>>,
    _ty_g: Ty<G, Pow<Y2, X2>>,
) -> Ty<Par<F, G>, Pow<Tup<Y1, Y2>, Tup<X1, X2>>> {
    unimplemented!()
}
/// `(f : (x1 => y1)) ⋀ (g : (x2 => y2))  =>  (f x g) : ((x1, x2) => (y1, y2))`.
pub fn par_tup_lam_ty<F: Prop, G: Prop, X1: Prop, X2: Prop, Y1: Prop, Y2: Prop>(
    _ty_f: Ty<F, Imply<X1, Y1>>,
    _ty_g: Ty<G, Imply<X2, Y2>>,
) -> Ty<Par<F, G>, Imply<Tup<X1, X2>, Tup<Y1, Y2>>> {
    unimplemented!()
}
/// `is_const(par_tup)`.
pub fn par_tup_is_const() -> IsConst<ParTup> {unimplemented!()}
/// `(id x id) == id`.
pub fn par_tup_id() -> Eq<Par<FId, FId>, FId> {unimplemented!()}
/// `(g1 x g2) . (f1 x f2)  ==  ((g1 . f1) x (g2 . f2))`.
pub fn par_tup_comp<F1: Prop, F2: Prop, G1: Prop, G2: Prop>() ->
    Eq<Comp<Par<G1, G2>, Par<F1, F2>>, Par<Comp<G1, F1>, Comp<G2, F2>>>
{unimplemented!()}
/// `inv(f x g)  ==  inv(f) x inv(g)`.
pub fn par_tup_inv<F: Prop, G: Prop>() -> Eq<Inv<Par<F, G>>, ParInv<F, G>>
{unimplemented!()}
/// `(f(i0) == o0) ⋀ (g(i1) == o1)  =>  (f x g)(i0, i1) == (o0, o1)`.
pub fn par_tup_def<F: Prop, G: Prop, I0: Prop, I1: Prop, O0: Prop, O1: Prop>(
    _eq0: Eq<App<F, I0>, O0>,
    _eq1: Eq<App<G, I1>, O1>,
) -> Eq<App<Par<F, G>, Tup<I0, I1>>, Tup<O0, O1>> {unimplemented!()}

/// `is_const(f) ⋀ is_const(g)  =>  is_const(f x g)`.
pub fn par_tup_app_is_const<F: Prop, G: Prop>(
    f: IsConst<F>,
    g: IsConst<G>
) -> IsConst<Par<F, G>> {app_is_const(par_tup_is_const(), tup_is_const(f, g))}

/// `f[g1 -> g2]`.
///
/// Normal path of 1 argument.
#[derive(Copy, Clone)]
pub struct Norm1<F, G1, G2>(pub Comp<Comp<G2, F>, Inv<G1>>);
/// `f[g]` of 1 argument.
pub type SymNorm1<F, G> = Norm1<F, G, G>;
/// `f[g1 x g2 -> g3]`.
///
/// Normal path of 2 arguments.
#[derive(Copy, Clone)]
pub struct Norm2<F, G1, G2, G3>(pub Comp<Comp<G3, F>, ParInv<G1, G2>>);
/// `f[g]` of 2 arguments.
pub type SymNorm2<F, G> = Norm2<F, G, G, G>;

/// `(f : a -> b) ⋀ (g1 : a -> c) ⋀ (g2 : b -> d)  =>  f[g1 -> g2] : c -> d`.
pub fn norm1_ty<F: Prop, G1: Prop, G2: Prop, A: Prop, B: Prop, C: Prop, D: Prop>(
    ty_f: Ty<F, Pow<B, A>>,
    ty_g1: Ty<G1, Pow<C, A>>,
    ty_g2: Ty<G2, Pow<D, B>>,
) -> Ty<Norm1<F, G1, G2>, Pow<D, C>> {
    let y2 = comp_ty(inv_ty(ty_g1), comp_ty(ty_f, ty_g2));
    eqx!(y2, norm1_def, tyl)
}
/// `(f : (a1, a2) -> b) ⋀ (g1 : a1 -> c1) ⋀ (g2 : a2 -> c2) ⋀ (g3 : b -> d)  =>
///   f[g1 x g2 -> g3] : (c1, c2) -> d`.
pub fn norm2_ty<F: Prop, G1: Prop, G2: Prop, G3: Prop,
    A1: Prop, A2: Prop, B: Prop, C1: Prop, C2: Prop, D: Prop> (
    ty_f: Ty<F, Pow<B, Tup<A1, A2>>>,
    ty_g1: Ty<G1, Pow<C1, A1>>,
    ty_g2: Ty<G2, Pow<C2, A2>>,
    ty_g3: Ty<G3, Pow<D, B>>
) -> Ty<Norm2<F, G1, G2, G3>, Pow<D, Tup<C1, C2>>> {
    path_semantics::ty_in_left_arg(norm1_ty(ty_f, par_tup_fun_ty(ty_g1, ty_g2), ty_g3),
        eq::symmetry(eq_norm2_norm1()))
}
/// `(f : a -> a) ⋀ (g : a -> b)  =>  f[g] : b -> b`.
pub fn sym_norm1_ty<F: Prop, G: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<A, A>>,
    ty_g: Ty<G, Pow<B, A>>,
) -> Ty<SymNorm1<F, G>, Pow<B, B>> {norm1_ty(ty_f, ty_g.clone(), ty_g)}
/// `(f : (a, a) -> a) ⋀ (g : a -> b)  =>  f[g] : (b, b) -> b`.
pub fn sym_norm2_ty<F: Prop, G: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<A, Tup<A, A>>>,
    ty_g: Ty<G, Pow<B, A>>,
) -> Ty<SymNorm2<F, G>, Pow<B, Tup<B, B>>> {norm2_ty(ty_f, ty_g.clone(), ty_g.clone(), ty_g)}
/// `f[g1 -> g2]  ==  (g2 . f) . inv(g1)`.
pub fn norm1_def<F: Prop, G1: Prop, G2: Prop>() ->
    Eq<Norm1<F, G1, G2>, Comp<Comp<G2, F>, Inv<G1>>> {eqx!(def Norm1)}
/// `f[g1 x g2 -> g3]  ==  (g3 . f) . (inv(g1) x inv(g2))`.
pub fn norm2_def<F: Prop, G1: Prop, G2: Prop, G3: Prop>() ->
    Eq<Norm2<F, G1, G2, G3>, Comp<Comp<G3, F>, ParInv<G1, G2>>> {eqx!(def Norm2)}
/// `f[g1 -> g2][g3 -> g4]  ==  f[(g3 . g1) -> (g4 . g2)]`.
pub fn norm1_comp<F: Prop, G1: Prop, G2: Prop, G3: Prop, G4: Prop>() ->
    Eq<Norm1<Norm1<F, G1, G2>, G3, G4>, Norm1<F, Comp<G3, G1>, Comp<G4, G2>>>
{
    let y = eq::transitivity(comp_eq_left(comp_assoc()), eq::symmetry(comp_assoc()));
    let y = eq::transitivity(eq::transitivity(y, comp_eq_right(comp_inv())), comp_eq_left(comp_assoc()));
    eqx!(eqx!(y, norm1_def, cr, cl, l), norm1_def, l, r)
}
/// `f[g1][g2]  ==  f[g2 . g1]` for 1 argument.
pub fn sym_norm1_comp<F: Prop, G1: Prop, G2: Prop>() ->
    Eq<SymNorm1<SymNorm1<F, G1>, G2>, SymNorm1<F, Comp<G2, G1>>>
{norm1_comp()}
/// `(f == h)  =>  f[g1 -> g2] == h[g1 -> g2]`.
pub fn norm1_eq<F: Prop, G1: Prop, G2: Prop, H: Prop>(x: Eq<F, H>) ->
    Eq<Norm1<F, G1, G2>, Norm1<H, G1, G2>> {eqx!(comp_eq_left(comp_eq_right(x)), norm1_def, eq)}
/// `(g1 == h)  =>  f[g1 -> g2] == f[h -> g2]`.
pub fn norm1_eq_in<F: Prop, G1: Prop, G2: Prop, H: Prop>(x: Eq<G1, H>) ->
    Eq<Norm1<F, G1, G2>, Norm1<F, H, G2>> {eqx!(comp_eq_right(inv_eq(x)), norm1_def, eq)}
/// `(g2 == h)  =>  f[g1 -> g2] == f[g1 -> h]`.
pub fn norm1_eq_out<F: Prop, G1: Prop, G2: Prop, H: Prop>(x: Eq<G2, H>) ->
    Eq<Norm1<F, G1, G2>, Norm1<F, G1, H>>
{eqx!(eqx!(comp_eq_left(comp_eq_left(x)), norm1_def, l), norm1_def, r)}
/// `(f == h)  =>  f[g1 x g2 -> g3] == h[g1 x g2 -> g3]`.
pub fn norm2_eq<F: Prop, G1: Prop, G2: Prop, G3: Prop, H: Prop>(x: Eq<F, H>) ->
    Eq<Norm2<F, G1, G2, G3>, Norm2<H, G1, G2, G3>>
{eqx!(comp_eq_left(comp_eq_right(x)), norm2_def, eq)}
/// `f[g1 x g2 -> g3]  ==  f[(g1 x g2) -> g3]`.
pub fn eq_norm2_norm1<F: Prop, G1: Prop, G2: Prop, G3: Prop>() ->
    Eq<Norm2<F, G1, G2, G3>, Norm1<F, Par<G1, G2>, G3>>
{eqx!(eqx!(comp_eq_right(eq::symmetry(par_tup_inv())), norm1_def, r), norm2_def, l)}
/// `f[g1 x g2 -> g3][g4 x g5 -> g6]  ==  f[(g1 x g2) -> g3][(g4 x g5) -> g6]`.
pub fn eq_norm2_norm1_comp<F: Prop, G1: Prop, G2: Prop, G3: Prop, G4: Prop, G5: Prop, G6: Prop>()
    -> Eq<Norm2<Norm2<F, G1, G2, G3>, G4, G5, G6>,
          Norm1<Norm1<F, Par<G1, G2>, G3>, Par<G4, G5>, G6>>
{eq::transitivity(norm2_eq(eq_norm2_norm1()), eq_norm2_norm1())}
/// `f[g1 x g2 -> g3][g4 x g5 -> g6]  ==  f[(g4 . g1) x (g5 . g2) -> (g6 . g3)]`.
pub fn norm2_comp<F: Prop, G1: Prop, G2: Prop, G3: Prop, G4: Prop, G5: Prop, G6: Prop>() ->
    Eq<Norm2<Norm2<F, G1, G2, G3>, G4, G5, G6>, Norm2<F, Comp<G4, G1>, Comp<G5, G2>, Comp<G6, G3>>>
{
    let (y0, y1) = eq_norm2_norm1_comp();
    let (y2, y3) = norm1_comp();
    let (y4, y5) = eq_norm2_norm1();
    let (x0, x1) = norm1_eq_in(par_tup_comp());
    (imply::transitivity(imply::transitivity(imply::transitivity(y0, y2), x0), y5),
     imply::transitivity(imply::transitivity(imply::transitivity(y4, x1), y3), y1))
}
/// `f[g1][g2]  ==  f[g2 . g1]` for 2 arguments.
pub fn sym_norm2_comp<F: Prop, G1: Prop, G2: Prop>() ->
    Eq<SymNorm2<SymNorm2<F, G1>, G2>, SymNorm2<F, Comp<G2, G1>>>
{norm2_comp()}
/// `f[id]  == f` for 1 argument.
pub fn sym_norm1_id<F: Prop>() -> Eq<SymNorm1<F, FId>, F> {
    let x = quality::to_eq(id_q());
    let x = eq::transitivity(eq::transitivity(comp_eq_right(x), comp_id_right()), comp_id_left());
    eqx!(x, norm1_def, l)
}
/// `f[id] == f` for 2 arguments.
pub fn sym_norm2_id<F: Prop>() -> Eq<SymNorm2<F, FId>, F> {
    let x = eqx!(comp_eq_right(inv_eq(par_tup_id())), norm1_def, eq);
    eq::transitivity(eq::transitivity(eq_norm2_norm1(), x), sym_norm1_id())
}
/// `id[f -> id] == inv(f)`.
pub fn norm1_inv<F: Prop>() -> Eq<Norm1<FId, F, FId>, Inv<F>> {
    eqx!(eq::transitivity(comp_eq_left(comp_id_left()), comp_id_left()), norm1_def, l)
}
/// `g2(f(inv(g1)(x))) == f[g1 -> g2](x)`.
pub fn eq_app_norm1<F: Prop, G1: Prop, G2: Prop, X: Prop>() ->
Eq<App<G2, App<F, App<Inv<G1>, X>>>, App<Norm1<F, G1, G2>, X>> {
    let x = eq::transitivity(eq_app_comp(), eq_app_comp());
    eqx!(x, norm1_def, am, r)
}
/// `g3(f(inv(g1 x g2)(x))) == f[g1 x g2 -> g3](x)`.
pub fn eq_app_norm2<F: Prop, G1: Prop, G2: Prop, G3: Prop, X: Prop>() ->
Eq<App<G3, App<F, App<Inv<Par<G1, G2>>, X>>>, App<Norm2<F, G1, G2, G3>, X>> {
    eq::in_right_arg(eq_app_norm1(), app_map_eq(eq::symmetry(eq_norm2_norm1())))
}
/// `(inv(g1) ~~ h1) ⋀ (inv(g1) ~~ h2) ⋀
///  (g1(b1) = a1) ⋀ (g2(b2) = a2) ⋀ (f(b1, b2) = c) ⋀ (g3(c) = d)  =>
///  f[g1 x g2 -> g3](a1, a2) = d`.
pub fn norm2_app<F: Prop, G1: Prop, G2: Prop, G3: Prop, H1: Prop, H2: Prop,
A1: Prop, A2: Prop, B1: Prop, B2: Prop, C: Prop, D: Prop>(
    q_inv_g1_h1: Q<Inv<G1>, H1>,
    q_inv_g2_h2: Q<Inv<G2>, H2>,
    eq_g1b1_a1: Eq<App<G1, B1>, A1>,
    eq_g2b2_a2: Eq<App<G2, B2>, A2>,
    eq_fb1b2_c: Eq<App<F, Tup<B1, B2>>, C>,
    eq_g3c_d: Eq<App<G3, C>, D>
) -> Eq<App<Norm2<F, G1, G2, G3>, Tup<A1, A2>>, D> {
    eq::in_left_arg(eq::transitivity(app_eq(eq::transitivity(app_eq(eq::in_left_arg(
        par_tup_def(inv_val(q_inv_g1_h1, eq_g1b1_a1), inv_val(q_inv_g2_h2, eq_g2b2_a2)),
        app_map_eq(eq::symmetry(par_tup_inv())))), eq_fb1b2_c)), eq_g3c_d), eq_app_norm2())
}
/// `(inv(g) ~~ h) ⋀ (g(b1) = a1) ⋀ (g(b2) = a2) ⋀ (f(b1, b2) = c) ⋀ (g(c) = d)  =>
///  f[g](a1, a2) = d`.
pub fn sym_norm2_app<F: Prop, G: Prop, H: Prop,
A1: Prop, A2: Prop, B1: Prop, B2: Prop, C: Prop, D: Prop>(
    q_inv_g_h: Q<Inv<G>, H>,
    eq_g1b1_a1: Eq<App<G, B1>, A1>,
    eq_g2b2_a2: Eq<App<G, B2>, A2>,
    eq_fb1b2_c: Eq<App<F, Tup<B1, B2>>, C>,
    eq_g3c_d: Eq<App<G, C>, D>
) -> Eq<App<SymNorm2<F, G>, Tup<A1, A2>>, D> {
    norm2_app(q_inv_g_h.clone(), q_inv_g_h, eq_g1b1_a1, eq_g2b2_a2, eq_fb1b2_c, eq_g3c_d)
}

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
