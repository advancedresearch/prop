//! Natural numbers.

use super::*;
use bool_alg::{Bool, Tr};

/// The type of natural numbers.
#[derive(Copy, Clone)]
pub struct Nat(());

/// The number `prev(a)` is the number right before `a`, if it exists.
///
/// This not an operation, but a reference to some proposition depending on `a`.
///
/// It is used to prevent collisions with other propositions where the identity might be
/// controlled by the scope, for example in `(x : nat)  =>  (x == 0) ⋁ (y : nat, x == y + 1)`.
///
/// A such statement in Prop can be changed into `(x : nat)  =>  (x == 0) ⋁ (x : nat, x == x + 1)`,
/// which is unsound.
///
/// To avoid this form of collision, the statement is encoded as:
/// `(x : nat)  =>  (x == 0) ⋁ (prev(x) : nat, x == prev(x) + 1)`.
pub struct Prev<A>(A);

/// `nat : type(0)`.
pub fn nat_ty() -> Ty<Nat, Type<Z>> {unimplemented!()}
/// `(x : nat)  =>  (x == 0) ⋁ ((prev(x) : nat) ⋀ (x == prev(x) + 1))`.
pub fn nat_def<X: Prop>(
    _x_ty: Ty<X, Nat>
) -> Either<Eq<X, Zero>, And<Ty<Prev<X>, Nat>, Eq<X, Inc<Prev<X>>>>> {unimplemented!()}
/// `(n : nat) ⋀ (n == n + 1)  =>  false`.
pub fn para_eq_inc<N: Prop>(_: And<Ty<N, Nat>, Eq<N, Inc<N>>>) -> False {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (n + 1 == m + 1)  =>  n == m`.
pub fn inc_eq_rev<N: Prop, M: Prop>(
    _ty_n: Ty<N, Nat>,
    _ty_m: Ty<M, Nat>,
    _: Eq<Inc<N>, Inc<M>>
) -> Eq<N, M> {unimplemented!()}
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

/// Used to get full Peano axioms.
///
/// Adds the final axiom required to make natural numbers equal to the model of the Peano axioms.
/// This final axiom states that there is no natural number before zero.
///
/// In the [Closed Natural Numbers](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#closed-natural-numbers)
/// formulation, this final axiom is too strong, since it is sufficient that the natural number
/// before zero is not unique (either none, multiple or non-constructive).
pub trait Peano {
    /// `(n : nat) ⋀ (0 == n + 1)  =>  false`.
    fn para_pre_zero<N: Prop>(_: And<Ty<N, Nat>, Eq<Zero, Inc<N>>>) -> False;
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
