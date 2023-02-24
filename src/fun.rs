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
//! If a function `f` has no inverse, then it is useful to prove `false^(inv(f) ~~ g)`.
//!
//! ### Function Extensionality
//!
//! For more information about function extensionality, see the `fun::fun_ext` module.
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
use qubit::{Qu, Qubit};
use hooo::{Exists, Para, Pow, Tauto, Theory};
use hooo::pow::PowExt;
use nat::{Nat, S, Z};
use univalence::HomEq3;

pub use app::*;
pub use comp::*;
pub use dup::*;
pub use feq::*;
pub use id::*;
pub use inv::*;
pub use is_const::*;
pub use norm::*;
pub use subst::*;
pub use tup::*;
pub use ty::*;

mod app;
mod comp;
mod dup;
mod feq;
mod id;
mod inv;
mod is_const;
mod norm;
mod subst;
mod tup;
mod ty;

pub mod bool_alg;
pub mod real;
pub mod eqx;
pub mod fnat;
pub mod fin;
pub mod fun_ext;
pub mod list;
pub mod phott;

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

/// `(\(a : x) = a) == id{a}`.
pub fn lam_id_eq<A: Prop, X: Prop>() -> Eq<LamId<A, X>, App<FId, X>> {unimplemented!()}

/// `(\(a : x) = a) ~~ id{x}`.
pub fn lam_id_q<A: Prop, X: Prop>() -> Q<LamId<A, X>, App<FId, X>> {
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
