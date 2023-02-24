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
pub use feq::*;
pub use id::*;
pub use inv::*;
pub use norm::*;
pub use subst::*;
pub use tup::*;

mod app;
mod comp;
mod feq;
mod id;
mod inv;
mod norm;
mod subst;
mod tup;

pub mod bool_alg;
pub mod real;
pub mod eqx;
pub mod fnat;
pub mod fin;
pub mod fun_ext;
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

/// `is_contr(a) := is_hprop(0, a)`.
pub type IsContr<A> = IsHProp<Z, A>;
/// `is_prop(a) := (~a == a)^true`.
pub type IsProp<A> = Tauto<Eq<Qu<A>, A>>;
/// `is_set(a) := is_prop(~a)`.
///
/// This is the same as `(~~a == ~a)^true`.
pub type IsSet<A> = IsProp<Qu<A>>;
/// `is_groupoid(a) := is_set(~a)`.
///
/// This is the same as `(~~~a == ~~a)^true`.
pub type IsGroupoid<A> = IsSet<Qu<A>>;
/// `is_hprop(n, a) := (qubit^n(a) == qubit^(n-1)(a))^true` where `qubit^(-1)(a) == true`.
pub type IsHProp<N, A> = Tauto<Eq<<S<N> as QuHLev>::Out<A>, <N as QuHLev>::Out<A>>>;
/// `is_ngroupoid(n, a) := is_hprop(n+2, a)`.
pub type IsNGroupoid<N, A> = IsHProp<S<S<N>>, A>;

/// Used to get repeated application of qubit `~` corresponding to homotopy levels.
pub trait QuHLev {
    /// The resulting type.
    type Out<A: Prop>: Prop;
}

impl QuHLev for Z {type Out<A: Prop> = True;}
impl<N: Nat> QuHLev for S<N> {type Out<A: Prop> = Qubit<N, A>;}

/// `is_contr(true)`.
pub fn is_contr_true() -> IsContr<True> {
    tauto!((True.map_any(), Qubit::<Z, True>::from(True).map_any()))
}
/// `is_prop(true)`.
pub fn is_prop_true() -> IsProp<True> {tauto!(eq_qu_true_true())}
/// `is_prop(false)`.
pub fn is_prop_false() -> IsProp<False> {tauto!(eq_qu_false_false())}
/// `a^b  =>  is_prop(a^b)`.
pub fn pow_to_is_prop<A: Prop, B: Prop>(x: Pow<A, B>) -> IsProp<Pow<A, B>> {
    x.lift().trans(pow_to_eq_qu)
}
/// `is_set(id{a})`.
pub fn is_set_id<A: Prop>() -> IsSet<App<FId, A>> {collapse_to_set_right(tauto!(id_q()))}
/// `is_set(not)`.
pub fn is_set_not() -> IsSet<bool_alg::FNot> {collapse_to_set_right(tauto!(bool_alg::not_q()))}
/// `is_contr(a)  =>  (a == true)^true`.
pub fn is_contr_to_tauto_eq_true<A: Prop>(x: IsContr<A>) -> Tauto<Eq<A, True>> {
    fn f<A: Prop>(x: Eq<Qubit<Z, A>, True>) -> Eq<A, True> {
        (True.map_any(), Qubit::<Z, A>::to(x.1(True)).map_any())
    }
    x.trans(f)
}
/// `(a == true)^true  =>  is_contr(a)`.
pub fn tauto_eq_true_to_is_contr<A: Prop>(x: Tauto<Eq<A, True>>) -> IsContr<A> {
    fn f<A: Prop>(x: Eq<A, True>) -> Eq<Qubit<Z, A>, True> {
        (True.map_any(), Qubit::<Z, A>::from(x.1(True)).map_any())
    }
    x.trans(f)
}
/// `is_contr(a)  =>  is_prop(a)`.
pub fn is_contr_to_is_prop<A: Prop>(x: IsContr<A>) -> IsProp<A> {
    use hooo::{tauto_qu_eq, tauto_eq_symmetry, tauto_eq_transitivity as trans};

    let y = is_contr_to_tauto_eq_true(x);
    trans(trans(tauto_qu_eq(y), is_prop_true()), tauto_eq_symmetry(y))
}
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
/// `a^true  =>  is_contr(a)`.
pub fn tauto_to_is_contr<A: Prop>(tauto_a: Tauto<A>) -> IsContr<A> {
    tauto_eq_true_to_is_contr(hooo::tauto_to_eq_true(tauto_a))
}
/// `is_contr(a)  =>  a^true`.
pub fn is_contr_to_tauto<A: Prop>(is_contr_a: IsContr<A>) -> Tauto<A> {
    hooo::tauto_from_eq_true(is_contr_to_tauto_eq_true(is_contr_a))
}
/// `a^true  ==  is_contr(a)`.
pub fn eq_tauto_is_contr<A: Prop>() -> Eq<Tauto<A>, IsContr<A>> {
    hooo::pow_eq_to_tauto_eq((tauto_to_is_contr, is_contr_to_tauto))(True)
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
    use qubit::{normalize, rev_normalize};
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
