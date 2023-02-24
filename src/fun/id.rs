//! Identity function.

use super::*;

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// `id`.
pub type Id<T, A> = App<App<FId, T>, A>;

/// `id{a} : a -> a`.
///
/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<App<FId, A>, Pow<A, A>> {unimplemented!()}
/// `is_const(id)`.
pub fn implicit_id_is_const() -> IsConst<FId> {unimplemented!()}
/// `(x : type(n)) ⋀ (a : x)  =>  id{x}(a) = a`.
///
/// Definition of identity function.
pub fn id_def<A: Prop, X: Prop, N: Nat>(
    _ty_x: Ty<X, Type<N>>,
    _ty_a: Ty<A, X>
) -> Eq<Id<X, A>, A> {unimplemented!()}
/// `inv(id{a}) ~~ id{a}`.
pub fn id_q<A: Prop>() -> Q<Inv<App<FId, A>>, App<FId, A>> {unimplemented!()}
/// `(f : a -> b) ⋀ (f . inv(f))  =>  id{b}`.
pub fn comp_right_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: Comp<F, Inv<F>>
) -> App<FId, B> {unimplemented!()}
/// `(f : a -> b) ⋀ id{b} => (f . inv(f))`.
pub fn id_to_comp_right_inv<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: App<FId, B>
) -> Comp<F, Inv<F>> {unimplemented!()}
/// `(f : a -> b) ⋀ (inv(f) . f) => id{a}`.
pub fn comp_left_inv_to_id<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: Comp<Inv<F>, F>
) -> App<FId, A> {unimplemented!()}
/// `(f : a -> b) ⋀ id{a} => (inv(f). f)`.
pub fn id_to_comp_left_inv<F: Prop, A: Prop, B: Prop>(
    _: Ty<F, Pow<B, A>>,
    _: App<FId, A>
) -> Comp<Inv<F>, F> {unimplemented!()}
