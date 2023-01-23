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
