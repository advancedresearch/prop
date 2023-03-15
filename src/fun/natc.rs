//! # Closed natural numbers

//! Closed natural numbers is a theory of natural numbers where 0 is both the first and the last
//! natural number. For more information, see
//! [reading sequence about closed natural numbers](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#closed-natural-numbers).
//!
//! Closed natural numbers occur frequently in computer science as modular arithmetic.
//! The difference between closed natural numbers and modular arithmetic is that in closed natural
//! numbers, you might have numbers that are infinite.
//!
//! For example, an infinite number `1 + 1 + 1 + 1 + ...` does not change identity by adding `1`
//! in front of it. Now, it is impossible to construct a such number without any assumptions.
//! However, one can *assume* that a such number exist and then use [addc_closed] to prove that
//! this number equals zero.
//!
//! Closed natural numbers is a [Robinson arithmetic](https://en.wikipedia.org/wiki/Robinson_arithmetic)
//! minus the first axiom that 0 is not the successor of any number `s(x) == 0  =>  false`,
//! plus a new axiom describing the closed property of addition ([addc_closed]):
//!
//! ```text
//! (n : nat_c) ⋀ (m : nat_c) ⋀ (n == add_c(s_c(n), m))  =>  n == m
//! ```
//!
//! Using symbolic distinction (see [sd]), one can show that it is not possible to construct such
//! numbers without making assumptions. Symbolic distinction can be used safely to extend logic,
//! but symbolic indistinction is not safe. Since this axiom implies symbolic distinction,
//! it is safe to use when reasoning about infinite series.
//!
//! ### Modular arithmetic
//!
//! To create a modular arithmetic `mod m + 1`, it suffices to assume `0 == add_c(s_c(0), m)`.
//!
//! For example, to get binary arithmetic, one can assume `0 == 2`, or `0 == add_c(s_c(0), s_c(0))`.
//!
//! One could also assume `1 == 3` or for any number `n`, `n == n + 2` to get binary arithmetic.

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

/// Closed multiplication.
#[derive(Copy, Clone)]
pub struct FMulc(());

/// `mul_c(a, b)`.
pub type Mulc<A, B> = App<FMulc, Tup<A, B>>;

/// `mul_c : (nat_c, nat_c) -> nat_c`.
pub fn mulc_ty() -> Ty<FMulc, Pow<Natc, Tup<Natc, Natc>>> {unimplemented!()}

/// `n : nat_c  =>  mul_c(n, 0_c) = 0_c`.
pub fn mulc_zc<N: Prop>(_ty_n: Ty<N, Natc>) -> Eq<Mulc<N, Zc>, Zc> {unimplemented!()}

/// `(n : nat_c) ⋀ (m : nat_c) ⋀ mul_c(n, s_c(m)) = add_c(mul_c(n, m), n)`.
pub fn mulc_sc<N: Prop, M: Prop>(
    _ty_n: Ty<N, Natc>,
    _ty_m: Ty<M, Natc>,
) -> Eq<Mulc<N, Sc<M>>, Addc<Mulc<N, M>, N>> {unimplemented!()}
