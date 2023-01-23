//! Natural numbers.

use super::*;
use bool_alg::{Bool, Tr};

/// The type of natural numbers.
#[derive(Copy, Clone)]
pub struct Nat(());

/// `nat : type(0)`.
pub fn nat_ty() -> Ty<Nat, Type<Z>> {unimplemented!()}
/// `(x : nat)  =>  (x == 0) ⋁ (y : nat, (\(y : nat) = x == (y + 1))(y))`.
pub fn nat_def<X: Prop, Y: Prop>(
    _x_ty: Ty<X, Nat>
) -> Either<Eq<X, Zero>, DepTupTy<Y, Nat, Lam<Ty<Y, Nat>, Eq<X, Inc<Y>>>>> {unimplemented!()}
/// `(n : nat) ⋀ (n == n + 1)  =>  false`.
pub fn para_eq_inc<N: Prop>(_: And<Ty<N, Nat>, Eq<N, Inc<N>>>) -> False {unimplemented!()}
/// Induction on natural numbers.
///
/// ```text
/// (p : nat -> bool)^true ⋀
/// (p(0) == true)^true ⋀
/// (p(n + 1) == true)^(n : nat)
/// ----------------------------
/// (p(n) == true)^(n : nat)
/// ```
pub fn induction<N: Prop, P: Prop>(
    _ty_p: Tauto<Ty<P, Pow<Bool, Nat>>>,
    _case_zero: Tauto<Eq<App<P, Zero>, Tr>>,
    _case_n: Pow<Eq<App<P, Inc<N>>, Tr>, Ty<N, Nat>>,
) -> Pow<Eq<App<P, N>, True>, Ty<N, Nat>> {unimplemented!()}
/// Type induction on natural numbers.
///
/// ```text
/// (p : nat -> type(0))^true ⋀
/// p(0)^true ⋀
/// p(n + 1)^(n : nat)
/// ----------------------------
/// p(n)^(n : nat)
/// ```
pub fn induction_ty<N: Prop, P: Prop>(
    _ty_p: Tauto<Ty<P, Pow<Type<Z>, Nat>>>,
    _case_zero: Tauto<App<P, Zero>>,
    _case_n: Pow<App<P, Inc<N>>, Ty<N, Nat>>,
) -> Pow<App<P, N>, Ty<N, Nat>> {unimplemented!()}

/// `(0 == 1)  =>  false`.
pub fn para_eq_zero_one(x: Eq<Zero, One>) -> False {para_eq_inc((zero_ty(), x))}
/// `(n : nat) ⋀ (0 == n + 1)  =>  false`.
pub fn para_pre_zero<N: Prop>((_ty_n, _x): And<Ty<N, Nat>, Eq<Zero, Inc<N>>>) -> False {
    unimplemented!()
}

/// Zero.
#[derive(Copy, Clone)]
pub struct Zero(());

/// `zero : nat`.
pub fn zero_ty() -> Ty<Zero, Nat> {unimplemented!()}

/// Successor.
#[derive(Copy, Clone)]
pub struct Succ(());

/// `succ : nat -> nat`.
pub fn succ_ty() -> Ty<Succ, Pow<Nat, Nat>> {unimplemented!()}

/// Increment.
pub type Inc<N> = App<Succ, N>;
/// One.
pub type One = Inc<Zero>;
/// Two.
pub type Two = Inc<One>;

/// Addition.
#[derive(Copy, Clone)]
pub struct Add(());

/// `a + b`.
pub type Plus<A, B> = App<Add, Tup<A, B>>;

/// `add : (nat, nat) -> nat`.
pub fn add_ty() -> Ty<Add, Pow<Nat, Tup<Nat, Nat>>> {unimplemented!()}
/// `(n : nat)  =>  add(0, n) = n`.
pub fn add_zero<N: Prop>(_n_ty: Ty<N, Nat>) -> Eq<Plus<Zero, N>, N> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat)  =>  add(n + 1, m) = add(n, m + 1)`.
pub fn add_succ<N: Prop, M: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>
) -> Eq<Plus<Inc<N>, M>, Plus<N, Inc<M>>> {unimplemented!()}

/// `1 : nat`.
pub fn one_ty() -> Ty<One, Nat> {app_fun_ty(succ_ty(), zero_ty())}
/// `2 : nat`.
pub fn two_ty() -> Ty<Two, Nat> {app_fun_ty(succ_ty(), one_ty())}
/// `1 + 1 == 2`.
pub fn eq_plus_one_one_two() -> Eq<Plus<One, One>, Two> {
    eq::transitivity(add_succ(zero_ty(), one_ty()), add_zero(two_ty()))
}
