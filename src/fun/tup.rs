//! Tuple.

use super::*;

/// Tuple.
#[derive(Copy, Clone)]
pub struct Tup<A, B>(A, B);

/// `(type(n), type(m)) : type(0)`.
pub fn tup_type_ty<N: Nat, M: Nat>() -> Ty<Tup<Type<N>, Type<M>>, Type<Z>> {
    unimplemented!()
}
/// `(a : x) ⋀ (b : y)  =>  (a, b) : (x, y)`.
pub fn tup_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _ty_a: Ty<A, X>,
    _ty_b: Ty<B, Y>
) -> Ty<Tup<A, B>, Tup<X, Y>> {unimplemented!()}
/// `is_const(a) ⋀ is_const(b)  =>  is_const((a, b))`.
pub fn tup_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Tup<A, B>> {
    unimplemented!()
}
/// `is_const((a, b))  =>  is_const(a)`.
pub fn tup_fst_const<A: Prop, B: Prop>(_: IsConst<Tup<A, B>>) -> IsConst<A> {unimplemented!()}
/// `is_const((a, b))  =>  is_const(b)`.
pub fn tup_snd_const<A: Prop, B: Prop>(_: IsConst<Tup<A, B>>) -> IsConst<B> {unimplemented!()}
/// `(a == b)  =>  (a, c) == (b, c)`.
pub fn tup_eq_fst<A: Prop, B: Prop, C: Prop>((ab, ba): Eq<A, B>) -> Eq<Tup<A, C>, Tup<B, C>> {
    (Rc::new(move |y| Tup(ab(y.0), y.1)), Rc::new(move |y| Tup(ba(y.0), y.1)))
}
/// `(a == b)  =>  (c, a) == (c, b)`.
pub fn tup_eq_snd<A: Prop, B: Prop, C: Prop>((ab, ba): Eq<A, B>) -> Eq<Tup<C, A>, Tup<C, B>> {
    (Rc::new(move |y| Tup(y.0, ab(y.1))), Rc::new(move |y| Tup(y.0, ba(y.1))))
}
/// `(c : d) ⋀ ((a, c) == (b, c))  =>  (a == b)`.
pub fn tup_rev_eq_fst<A: Prop, B: Prop, C: Prop, D: Prop>(
    _: Ty<C, D>,
    _: Eq<Tup<A, C>, Tup<B, C>>
) -> Eq<A, B> {unimplemented!()}
/// `(c : d) ⋀ ((c, a) == (c, b))  =>  (a == b)`.
pub fn tup_rev_eq_snd<A: Prop, B: Prop, C: Prop, D: Prop>(
    _: Ty<C, D>,
    _: Eq<Tup<C, A>, Tup<C, B>>
) -> Eq<A, B> {unimplemented!()}

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
/// `(id{a} x id{b}) == id{(a, b)}`.
pub fn par_tup_id<A: Prop, B: Prop>() -> Eq<Par<App<FId, A>, App<FId, B>>, App<FId, Tup<A, B>>> {
    unimplemented!()
}
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
