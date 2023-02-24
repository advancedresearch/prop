use super::*;

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
