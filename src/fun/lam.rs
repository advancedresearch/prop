use super::*;

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
