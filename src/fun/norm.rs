use super::*;

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
    ty::in_left_arg(norm1_ty(ty_f, par_tup_fun_ty(ty_g1, ty_g2), ty_g3),
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
    let y = eq::transitivity(eq::transitivity(y, comp_eq_right(eq_comp_inv())),
        comp_eq_left(comp_assoc()));
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
/// `(f : a -> a)  =>  (f[id{a}] == f)` for 1 argument.
pub fn sym_norm1_id<F: Prop, A: Prop, N: Nat>(
    ty_a: Ty<A, Type<N>>,
    ty_f: Ty<F, Pow<A, A>>
) -> Eq<SymNorm1<F, App<FId, A>>, F> {
    let x = eq::transitivity(eq::transitivity(comp_eq_right(quality::to_eq(id_q())),
        comp_id_right(comp_ty(ty_f.clone(), id_ty(ty_a)))), comp_id_left(ty_f));
    eqx!(x, norm1_def, l)
}
/// `(f : a -> b)  =>  (f[id{a} -> id{b}] == f)` for 1 argument.
pub fn norm1_id<F: Prop, A: Prop, B: Prop, N: Nat>(
    ty_b: Ty<B, Type<N>>,
    ty_f: Ty<F, Pow<B, A>>
) -> Eq<Norm1<F, App<FId, A>, App<FId, B>>, F> {
    let x = eq::transitivity(eq::transitivity(comp_eq_right(quality::to_eq(id_q())),
        comp_id_right(comp_ty(ty_f.clone(), id_ty(ty_b)))), comp_id_left(ty_f));
    eqx!(x, norm1_def, l)
}
/// `(f : (a, a) -> a)  =>  f[id{a}] == f` for 2 arguments.
pub fn sym_norm2_id<F: Prop, A: Prop, N: Nat>(
    ty_a: Ty<A, Type<N>>,
    ty_f: Ty<F, Pow<A, Tup<A, A>>>
) -> Eq<SymNorm2<F, App<FId, A>>, F> {
    let x: Eq<Norm1<F, Par<App<FId, A>, App<FId, A>>, App<FId, A>>, _> = eqx!(comp_eq_right(inv_eq(par_tup_id())), norm1_def, eq);
    eq::transitivity(eq::transitivity(eq_norm2_norm1(), x), norm1_id(ty_a, ty_f))
}
/// `(f : a -> a)  =>  id{a}[f -> id{a}] == inv(f)`.
pub fn norm1_inv<F: Prop, A: Prop, N: Nat>(
    ty_a: Ty<A, Type<N>>,
    ty_f: Ty<F, Pow<A, A>>
) -> Eq<Norm1<App<FId, A>, F, App<FId, A>>, Inv<F>> {
    let x = eq::transitivity(comp_eq_left(comp_id_left(id_ty(ty_a))), comp_id_left(inv_ty(ty_f)));
    eqx!(x, norm1_def, l)
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
