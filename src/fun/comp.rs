use super::*;

/// Composition.
#[derive(Copy, Clone)]
pub struct FComp(());

/// `is_const(comp)`.
pub fn fcomp_is_const() -> IsConst<FComp> {unimplemented!()}

/// `f . g`.
pub type Comp<F, G> = App<FComp, Tup<F, G>>;

/// `(f : x -> y) ⋀ (g : y -> z)  =>  (g . f) : x -> z`.
///
/// Type of composition.
pub fn comp_ty<F: Prop, G: Prop, X: Prop, Y: Prop, Z: Prop>(
    _ty_f: Ty<F, Pow<Y, X>>,
    _ty_g: Ty<G, Pow<Z, Y>>
) -> Ty<Comp<G, F>, Pow<Z, X>> {unimplemented!()}
/// `inv(g . f) => (inv(f) . inv(g))`.
pub fn comp_rev_inv<F: Prop, G: Prop>(_: Inv<Comp<G, F>>) -> Comp<Inv<F>, Inv<G>> {
    unimplemented!()
}
/// `(inv(f) . inv(g)) => inv(g . f)`.
pub fn comp_inv<F: Prop, G: Prop>(_: Comp<Inv<F>, Inv<G>>) -> Inv<Comp<G, F>> {
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
/// `(f : a -> b)  =>  (id{b} . f == f)`.
pub fn comp_id_left<F: Prop, A: Prop, B: Prop>(
    _ty_f: Ty<F, Pow<B, A>>
) -> Eq<Comp<App<FId, B>, F>, F> {unimplemented!()}
/// `(f : a -> b)  =>  (f . id{a} == f)`.
pub fn comp_id_right<F: Prop, A: Prop, B: Prop>(
    _ty_f: Ty<F, Pow<B, A>>
) -> Eq<Comp<F, App<FId, A>>, F> {unimplemented!()}
/// `~f ⋀ ~g  =>  ~(g . f)`.
pub fn comp_qu<F: Prop, G: Prop>(_: Qu<F>, _: Qu<G>) -> Qu<Comp<G, F>> {unimplemented!()}

/// `is_const(f) ⋀ is_const(g)  =>  is_const(g . f)`.
pub fn comp_is_const<F: Prop, G: Prop>(a: IsConst<F>, b: IsConst<G>) -> IsConst<Comp<G, F>> {
    app_is_const(fcomp_is_const(), tup_is_const(b, a))
}
/// `~inv(f) ⋀ ~inv(g)  =>  ~inv(g . f)`.
pub fn comp_inv_qu<F: Prop, G: Prop>(x: Qu<Inv<F>>, y: Qu<Inv<G>>) -> Qu<Inv<Comp<G, F>>> {
    qubit::in_arg(comp_qu(y, x), tauto!(eq_comp_inv()))
}
/// `(inv(f) . inv(g))  ==  inv(g . f)`.
pub fn eq_comp_inv<F: Prop, G: Prop>() -> Eq<Comp<Inv<F>, Inv<G>>, Inv<Comp<G, F>>> {
    (Rc::new(comp_inv), Rc::new(comp_rev_inv))
}
/// `(g . f)(x) == g(f(x))`.
pub fn eq_app_comp<F: Prop, G: Prop, X: Prop>() -> Eq<App<G, App<F, X>>, App<Comp<G, F>, X>> {
    (Rc::new(move |x| app_to_comp(x)), Rc::new(move |x| comp_to_app(x)))
}
/// `(g . f) ⋀ (g == h)  =>  (h . f)`.
pub fn comp_in_left_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<G, H>) -> Comp<H, F> {
    app_eq(tup_eq_fst(y)).0(x)
}
/// `(g . f) ⋀ (f == h)  =>  (g . h)`.
pub fn comp_in_right_arg<F: Prop, G: Prop, H: Prop>(x: Comp<G, F>, y: Eq<F, H>) -> Comp<G, H> {
    app_eq(tup_eq_snd(y)).0(x)
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
/// `~(f . inv(f)) ⋀ ((g . f) == (h . f)) ⋀ (f : a -> x) ⋀ (g : x -> y) ⋀ (h : x -> y)  =>  g == h`.
pub fn epic<F: Prop, G: Prop, H: Prop, X: Prop, Y: Prop, A: Prop>(
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
pub fn monic<F: Prop, G: Prop, H: Prop, X: Prop, Y: Prop, A: Prop>(
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
/// `(f(a) == b) ⋀ (g(b) == c)  =>  g(f(a)) == c`.
pub fn comp_app<F: Prop, G: Prop, A: Prop, B: Prop, C: Prop>(
    x: Eq<App<F, A>, B>,
    y: Eq<App<G, B>, C>
) -> Eq<App<G, App<F, A>>, C> {eq::transitivity(app_eq(x), y)}
/// `(f(a) == b) ⋀ (g(b) == c) ⋀ (h == (g . f))  =>  h(a) == c`.
pub fn comp_app_def<F: Prop, G: Prop, H: Prop, A: Prop, B: Prop, C: Prop>(
    x: Eq<App<F, A>, B>,
    y: Eq<App<G, B>, C>,
    z: Eq<H, Comp<G, F>>
) -> Eq<App<H, A>, C> {
    eq::transitivity(app_map_eq(z), eq::in_left_arg(comp_app(x, y), eq_app_comp()))
}
