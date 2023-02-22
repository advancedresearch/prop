//! Identity function.

use super::*;

/// Identity function.
#[derive(Clone, Copy)]
pub struct FId(());

/// `id`.
pub type Id<A> = App<FId, A>;

/// `id{a} : a -> a`.
///
/// Type of Id.
pub fn id_ty<A: Prop>() -> Ty<FId, Pow<A, A>> {unimplemented!()}
/// `is_const(id)`.
pub fn id_is_const() -> IsConst<FId> {unimplemented!()}

/// `(x : type(n)) ⋀ (a : x)  =>  id(a) = a`.
///
/// Definition of identity function.
pub fn id_def<A: Prop, X: Prop, N: Nat>(
    _ty_x: Ty<X, Type<N>>,
    _ty_a: Ty<A, X>
) -> Eq<Id<A>, A> {unimplemented!()}
/// `inv(id) ~~ id`.
pub fn id_q() -> Q<Inv<FId>, FId> {unimplemented!()}
/// `(f . inv(f)) => id`.
pub fn comp_right_inv_to_id<F: Prop>(_: Comp<F, Inv<F>>) -> FId {unimplemented!()}
/// `id => (f . inv(f))`.
pub fn id_to_comp_right_inv<F: Prop>(_: FId) -> Comp<F, Inv<F>> {unimplemented!()}
/// `(inv(f) . f) => id`.
pub fn comp_left_inv_to_id<F: Prop>(_: Comp<Inv<F>, F>) -> FId {unimplemented!()}
/// `id => (inv(f). f)`.
pub fn id_to_comp_left_inv<F: Prop>(_: FId) -> Comp<Inv<F>, F> {unimplemented!()}
