use super::*;

/// Imaginary inverse.
#[derive(Copy, Clone)]
pub struct FInv(());

/// `is_const(inv)`.
pub fn finv_is_const() -> IsConst<FInv> {unimplemented!()}

/// `inv(f)`.
pub type Inv<F> = App<FInv, F>;

/// Inverse type `(f : x -> y) => (inv(f) : y -> x)`.
pub fn inv_ty<F: Prop, X: Prop, Y: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>
) -> Ty<Inv<F>, Pow<X, Y>> {unimplemented!()}
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