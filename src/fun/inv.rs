//! # Imaginary Inverse
//!
//! The syntax `~x` uses `Qu<X>` from the [qubit] module,
//! and the syntax `x ~~ y` uses `Q<X, Y>` from the [quality] module.
//!
//! This model uses [imaginary inverse](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip/imaginary-inverse.pdf)
//! `inv(f)` with `~inv(f)` as a proof of inverse of `f`.
//! Here, `~` means the path semantical qubit operator, such that:
//!
//! ```text
//! (inv(f) ~~ g) => ~inv(f)
//! ```
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
/// `inv(id{x}) == id{x}`.
pub fn id_inv<X: Prop>() -> Eq<Inv<App<FId, X>>, App<FId, X>> {unimplemented!()}
/// `~(f . inv(f)) ⋀ (f : a -> b) ⋀ (f . inv(f))  =>  id{b}`.
pub fn comp_right_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Qu<Comp<F, Inv<F>>>,
    _: Ty<F, Pow<B, A>>,
    _: Comp<F, Inv<F>>
) -> App<FId, B> {unimplemented!()}
/// `~(f . inv(f)) ⋀ (f : a -> b) ⋀ id{b}  =>  (f . inv(f))`.
pub fn id_to_comp_right_inv<F: Prop, A: Prop, B: Prop>(
    _: Qu<Comp<F, Inv<F>>>,
    _: Ty<F, Pow<B, A>>,
    _: App<FId, B>
) -> Comp<F, Inv<F>> {unimplemented!()}
/// `~(inv(f) . f) ⋀ (f : a -> b) ⋀ (inv(f) . f)  =>  id{a}`.
pub fn comp_left_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Qu<Comp<Inv<F>, F>>,
    _: Ty<F, Pow<B, A>>,
    _: Comp<Inv<F>, F>
) -> App<FId, A> {unimplemented!()}
/// `~(inv(f) . f) ⋀ (f : a -> b) ⋀ id{a}  =>  (inv(f). f)`.
pub fn id_to_comp_left_inv<F: Prop, A: Prop, B: Prop>(
    _: Qu<Comp<Inv<F>, F>>,
    _: Ty<F, Pow<B, A>>,
    _: App<FId, A>
) -> Comp<Inv<F>, F> {unimplemented!()}
/// `inv(g . f) => (inv(f) . inv(g))`.
pub fn comp_rev_inv<F: Prop, G: Prop>(_: Inv<Comp<G, F>>) -> Comp<Inv<F>, Inv<G>> {
    unimplemented!()
}
/// `(inv(f) . inv(g)) => inv(g . f)`.
pub fn comp_inv<F: Prop, G: Prop>(_: Comp<Inv<F>, Inv<G>>) -> Inv<Comp<G, F>> {
    unimplemented!()
}

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
/// `~f ⋀ (inv(f)(a) == b)  =>  (f(b) == a)`.
pub fn inv_rev_val_qu<F: Prop, A: Prop, B: Prop>(
    qu_f: Qu<F>,
    x: Eq<App<Inv<F>, A>, B>
) -> Eq<App<F, B>, A> {
    eq::in_left_arg(inv_val_qu(qu_double(qu_f.clone()), x), app_map_eq(involve_eq()))
}
/// `~f ⋀ ~inv(f)  =>  (f(a) == b) == (inv(f)(b) == a)`.
pub fn qu_to_app_eq<A: Prop, B: Prop, F: Prop>(
    qu_f: Qu<F>, qu_inv_f: Qu<Inv<F>>
) -> Eq<Eq<App<F, A>, B>, Eq<App<Inv<F>, B>, A>> {
    (Rc::new(move |y| inv_val_qu(qu_inv_f.clone(), y)),
     Rc::new(move |y| inv_rev_val_qu(qu_f.clone(), y)))
}
/// `inv(f) == g  =>  inv(g) == f`.
pub fn inv_swap_eq<F: Prop, G: Prop>(x: Eq<Inv<F>, G>) -> Eq<Inv<G>, F> {
    eq::symmetry(eq::in_left_arg(inv_eq(x), involve_eq()))
}
/// `inv(f) == inv(g)  =>  f == g`.
pub fn inv_rev_eq<F: Prop, G: Prop>(x: Eq<Inv<F>, Inv<G>>) -> Eq<F, G> {
    eq::in_right_arg(eq::in_left_arg(inv_eq(x), involve_eq()), involve_eq())
}
/// `inv(id{a}) ~~ id{a}`.
pub fn id_q<A: Prop>() -> Q<Inv<App<FId, A>>, App<FId, A>> {self_inv_to_q(id_inv())}
/// `(f : A -> B) => ((f ~~ inv(f)) : ((A -> B) ~~ (B -> A)))`.
pub fn self_inv_ty<F: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>
) -> Ty<Q<F, Inv<F>>, Q<Pow<B, A>, Pow<A, B>>> {ty::q_formation(ty_f.clone(), inv_ty(ty_f))}
/// `(f : a -> a) ⋀ (inv(f) == f) => ((f . f) == id{a})`.
pub fn self_inv_to_eq_id<F: Prop, A: Prop>(
    ty_f: Ty<F, Pow<A, A>>,
    eq_f: Eq<Inv<F>, F>
) -> Eq<Comp<F, F>, App<FId, A>> {
    let x = inv::self_inv_to_q(eq_f.clone());
    let qu_f = qubit::Qubit::from_q(quality::right(x.clone()));
    let qu_inv_f = qubit::Qubit::from_q(quality::left(x));
    let qu_comp_f_inv_f = comp::comp_qu(qu_inv_f, qu_f);
    let qu_comp_f_inv_f_2 = qu_comp_f_inv_f.clone();
    let ty_f_2 = ty_f.clone();
    let eq_f_2 = eq_f.clone();
    (
        Rc::new(move |x| comp_right_inv_to_id(qu_comp_f_inv_f.clone(), ty_f_2.clone(),
            comp_in_right_arg(x, eq::symmetry(eq_f_2.clone())))),
        Rc::new(move |x| comp_in_right_arg(id_to_comp_right_inv(qu_comp_f_inv_f_2.clone(),
            ty_f.clone(), x), eq_f.clone())),
    )
}
/// `~(f . inv(f)) ⋀ ((g . f) == (h . f)) ⋀ (f : a -> x) ⋀ (g : x -> y) ⋀ (h : x -> y)  =>  g == h`.
pub fn split_epic<F: Prop, G: Prop, H: Prop, X: Prop, Y: Prop, A: Prop>(
    qu_comp_f_inv_f: Qu<Comp<F, Inv<F>>>,
    x: Eq<Comp<G, F>, Comp<H, F>>,
    ty_f: Ty<F, Pow<X, A>>,
    ty_g: Ty<G, Pow<Y, X>>,
    ty_h: Ty<H, Pow<Y, X>>,
) -> Eq<G, H> {
    let x: Eq<Comp<Comp<G, F>, Inv<F>>, Comp<Comp<H, F>, Inv<F>>> = comp_eq_left(x);
    let x: Eq<Comp<G, Comp<F, Inv<F>>>, _> = eq::in_left_arg(x, eq::symmetry(comp_assoc()));
    let x: Eq<_, Comp<H, Comp<F, Inv<F>>>> = eq::in_right_arg(x, eq::symmetry(comp_assoc()));
    let y: Eq<Comp<F, Inv<F>>, Id<X>> = eq_comp_right_inv_id(qu_comp_f_inv_f, ty_f);
    let x: Eq<Comp<G, Id<X>>, _> = eq::in_left_arg(x, comp_eq_right(y.clone()));
    let x: Eq<_, Comp<H, Id<X>>> = eq::in_right_arg(x, comp_eq_right(y));
    let x: Eq<G, _> = eq::in_left_arg(x, comp_id_right(ty_g));
    let x: Eq<_, H> = eq::in_right_arg(x, comp_id_right(ty_h));
    x
}
/// `~(inv(f) . f) ⋀ ((f . g) == (f . h)) ⋀ (f : x -> y) ⋀ (g : a -> x) ⋀ (h : a -> x)  =>  g == h`.
pub fn split_monic<F: Prop, G: Prop, H: Prop, X: Prop, Y: Prop, A: Prop>(
    qu_comp_inv_f_f: Qu<Comp<Inv<F>, F>>,
    x: Eq<Comp<F, G>, Comp<F, H>>,
    ty_f: Ty<F, Pow<Y, X>>,
    ty_g: Ty<G, Pow<X, A>>,
    ty_h: Ty<H, Pow<X, A>>,
) -> Eq<G, H> {
    let x: Eq<Comp<Inv<F>, Comp<F, G>>, Comp<Inv<F>, Comp<F, H>>> = comp_eq_right(x);
    let x: Eq<Comp<Comp<Inv<F>, F>, G>, _> = eq::in_left_arg(x, comp_assoc());
    let x: Eq<_, Comp<Comp<Inv<F>, F>, H>> = eq::in_right_arg(x, comp_assoc());
    let y: Eq<Comp<Inv<F>, F>, Id<X>> = eq_comp_left_inv_id(qu_comp_inv_f_f, ty_f);
    let x: Eq<Comp<Id<X>, G>, _> = eq::in_left_arg(x, comp_eq_left(y.clone()));
    let x: Eq<_, Comp<Id<X>, H>> = eq::in_right_arg(x, comp_eq_left(y));
    let x: Eq<G, _> = eq::in_left_arg(x, comp_id_left(ty_g));
    let x: Eq<_, H> = eq::in_right_arg(x, comp_id_left(ty_h));
    x
}
/// `~(inv(f) . f) ⋀ (f : a -> b)  =>  (inv(f) . f) == id{a}`.
pub fn eq_comp_left_inv_id<F: Prop, A: Prop, B: Prop>(
    qu_comp_inv_f_f: Qu<Comp<Inv<F>, F>>,
    ty_f: Ty<F, Pow<B, A>>
) -> Eq<Comp<Inv<F>, F>, Id<A>> {
    let ty_f2 = ty_f.clone();
    let qu_comp_inv_f_f_2 = qu_comp_inv_f_f.clone();
    (Rc::new(move |x| comp_left_inv_to_id(qu_comp_inv_f_f.clone(), ty_f.clone(), x)),
     Rc::new(move |x| id_to_comp_left_inv(qu_comp_inv_f_f_2.clone(), ty_f2.clone(), x)))
}
/// `~(f . inv(f)) ⋀ (f : a -> b)  =>  (f . inv(f)) == id{b}`.
pub fn eq_comp_right_inv_id<F: Prop, A: Prop, B: Prop>(
    qu_comp_f_inv_f: Qu<Comp<F, Inv<F>>>,
    ty_f: Ty<F, Pow<B, A>>
) -> Eq<Comp<F, Inv<F>>, Id<B>> {
    let ty_f2 = ty_f.clone();
    let qu_comp_f_inv_f_2 = qu_comp_f_inv_f.clone();
    (Rc::new(move |x| comp_right_inv_to_id(qu_comp_f_inv_f.clone(), ty_f.clone(), x)),
     Rc::new(move |x| id_to_comp_right_inv(qu_comp_f_inv_f_2.clone(), ty_f2.clone(), x)))
}
/// `~inv(f) ⋀ ~inv(g)  =>  ~inv(g . f)`.
pub fn comp_inv_qu<F: Prop, G: Prop>(x: Qu<Inv<F>>, y: Qu<Inv<G>>) -> Qu<Inv<Comp<G, F>>> {
    qubit::in_arg(comp_qu(y, x), tauto!(eq_comp_inv()))
}
/// `(inv(f) . inv(g))  ==  inv(g . f)`.
pub fn eq_comp_inv<F: Prop, G: Prop>() -> Eq<Comp<Inv<F>, Inv<G>>, Inv<Comp<G, F>>> {
    (Rc::new(comp_inv), Rc::new(comp_rev_inv))
}
