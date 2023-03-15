//! Closed natural numbers.

use super::*;

/// The type of closed natural numbers.
#[derive(Copy, Clone)]
pub struct Natc(());

/// `nat_c : type(0)`.
pub fn natc_ty() -> Ty<Natc, Type<Z>> {unimplemented!()}

/// `n : nat_c  =>  (n == 0_c) ⋁ ∃ m : nat_c { s_c(m) == n }`.
pub fn natc_def<N: Prop, M: Prop>(
    _: Ty<N, Natc>
) -> Or<Eq<N, Zc>, Exists<Ty<M, Natc>, Eq<Sc<M>, N>>> {unimplemented!()}

/// Closed zero.
#[derive(Copy, Clone)]
pub struct Zc(());

/// `0_c : nat_c`.
pub fn zeroc_ty() -> Ty<Zc, Natc> {unimplemented!()}

/// Closed successor function.
#[derive(Copy, Clone)]
pub struct FSc(());

/// `s_c(n)`.
pub type Sc<N> = App<FSc, N>;

/// `s_c : nat_c -> nat_c`.
pub fn sc_ty() -> Ty<FSc, Pow<Natc, Natc>> {unimplemented!()}

/// `n : nat_c  =>  s_c(n) : nat_c`.
pub fn sc_def<N: Prop>(_ty_n: Ty<N, Natc>) -> Ty<Sc<N>, Natc> {unimplemented!()}

/// `(s_c(n) == s_c(m))  =>  (n == m)`.
pub fn sc_eq_rev<N: Prop, M: Prop>(_: Eq<Sc<N>, Sc<M>>) -> Eq<N, M> {unimplemented!()}

/// Closed addition.
#[derive(Copy, Clone)]
pub struct FAddc(());

/// `add_c(a, b)`.
pub type Addc<A, B> = App<FAddc, Tup<A, B>>;

/// `add_c : (nat_c, nat_c) -> nat_c`.
pub fn addc_ty() -> Ty<FAddc, Pow<Natc, Tup<Natc, Natc>>> {unimplemented!()}

/// `n : nat_c  =>  add_c(n, 0_c) = n`.
pub fn addc_zeroc<N: Prop>(_ty_n: Ty<N, Natc>) -> Eq<Addc<N, Zc>, N> {unimplemented!()}

/// `(s_c(n) : nat_c) ⋀ (m : nat_c)  =>  add_c(n, s_c(m)) = s_c(add_c(n, m))`.
pub fn addc_zc<N: Prop, M: Prop>(
    _ty_sc_n: Ty<Sc<N>, Natc>,
    _ty_m: Ty<M, Natc>
) -> Eq<Addc<N, Sc<M>>, Sc<Addc<N, M>>> {unimplemented!()}

/// `(n : nat_c) ⋀ (m : nat_c) ⋀ (n == add_c(s_c(n), m))  =>  n == m`.
pub fn addc_closed<N: Prop, M: Prop>(
    _ty_n: Ty<N, Natc>,
    _ty_m: Ty<M, Natc>,
    _: Eq<N, Addc<Sc<N>, M>>
) -> Eq<N, M> {unimplemented!()}
