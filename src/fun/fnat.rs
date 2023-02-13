//! Natural numbers.

use super::*;
use bool_alg::{Bool, Tr};

/// The type of natural numbers.
#[derive(Copy, Clone)]
pub struct Nat(());

/// The number `prev(a)` is the number right before `a`, if it exists.
///
/// This not an operation, but a reference to some natural number depending on `a`.
///
/// It is used to prevent collisions with other propositions where the identity might be
/// controlled by the scope, for example in `(x : nat)  =>  (x == 0) ⋁ ((y : nat) ⋀ (x == y + 1))`.
///
/// A such statement in Prop can be changed into
/// `(x : nat)  =>  (x == 0) ⋁ ((x : nat) ⋀ (x == x + 1))`, which is unsound.
///
/// To avoid this form of collision, the statement is encoded as:
/// `(x : nat)  =>  (x == 0) ⋁ ((prev(x) : nat) ⋀ (x == prev(x) + 1))`.
#[derive(Clone)]
pub struct Prev<A>(A);

/// `nat : type(0)`.
pub fn nat_ty() -> Ty<Nat, Type<Z>> {unimplemented!()}
/// `is_const(nat)`.
pub fn nat_is_const() -> IsConst<Nat> {unimplemented!()}
/// `(x : nat)  =>  (x == 0) ⋁ ((prev(x) : nat) ⋀ (x == prev(x) + 1))`.
pub fn nat_def<X: Prop>(
    _x_ty: Ty<X, Nat>
) -> Either<Eq<X, Zero>, And<Ty<Prev<X>, Nat>, Eq<X, Inc<Prev<X>>>>> {unimplemented!()}
/// `(n : nat) ⋀ (n == n + 1)  =>  false`.
pub fn para_eq_inc<N: Prop>(_: And<Ty<N, Nat>, Eq<N, Inc<N>>>) -> False {unimplemented!()}
/// `(n : nat) ⋀ (0 == n + 1)  =>  false`.
pub fn para_pre_zero<N: Prop>(_: And<Ty<N, Nat>, Eq<Zero, Inc<N>>>) -> False {unimplemented!()}
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
/// (p(0) == tr)^true ⋀
/// (p(n + 1) == tr)^(n : nat)
/// ----------------------------
/// (p(n) == tr)^(n : nat)
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
/// `x^(n : nat)  =>  (x[n := succ(n)])^(succ(n) : nat)`.
pub fn subst_induction<N: Prop, X: Prop, M: Prop>(
    _: Pow<X, Ty<N, Nat>>
) -> Pow<Subst<X, N, Inc<N>>, Ty<Inc<N>, Nat>> {unimplemented!()}
/// `∃ 0 : nat { x } ⋀ ∃ succ(n) : nat { x }  =>  x`.
pub fn nat_exists<N: VProp, X: Prop>(
    _exists_zero_x: Exists<Ty<Zero, Nat>, X>,
    _exists_succ_n_x: Exists<Ty<Inc<N>, Nat>, X>
) -> X {unimplemented!()}

/// `succ(n)[n := a]  ==  succ(a)`.
pub fn subst_inc<N: Prop, A: Prop>() -> Eq<Subst<Inc<N>, N, A>, Inc<A>> {
    eq::transitivity(eq::transitivity(subst_app(), app_map_eq(subst_const(succ_is_const()))),
        app_eq(subst_trivial()))
}
/// `(0 == 1)  =>  false`.
pub fn para_eq_zero_one(x: Eq<Zero, One>) -> False {para_eq_inc((zero_ty(), x))}
/// `f : nat -> nat ⋀ g : nat -> nat ⋀
/// (f(0) == g(0))^true ⋀ (f(succ(n)) == g(succ(n)))^(succ(n) : nat)  =>  (f == g)`.
pub fn nat1_fun_ext<N: VProp, F: Prop, G: Prop>(
    ty_f: Ty<F, Pow<Nat, Nat>>,
    ty_g: Ty<G, Pow<Nat, Nat>>,
    case_zero: Tauto<Eq<App<F, Zero>, App<G, Zero>>>,
    case_succ: Pow<Eq<App<F, Inc<N>>, App<G, Inc<N>>>, Ty<Inc<N>, Nat>>
) -> Eq<F, G> {
    nat_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_zero)),
               app_fun_ext(ty_f, ty_g, case_succ))
}

/// Zero.
#[derive(Copy, Clone)]
pub struct Zero(());

/// `zero : nat`.
pub fn zero_ty() -> Ty<Zero, Nat> {unimplemented!()}
/// `is_const(zero)`.
pub fn zero_is_const() -> IsConst<Zero> {unimplemented!()}

/// Successor.
#[derive(Copy, Clone)]
pub struct Succ(());

/// `succ : nat -> nat`.
pub fn succ_ty() -> Ty<Succ, Pow<Nat, Nat>> {unimplemented!()}
/// `is_const(succ)`.
pub fn succ_is_const() -> IsConst<Succ> {unimplemented!()}

/// `is_const(n)  =>  is_const(succ(n))`.
pub fn inc_is_const<N: Prop>(n_is_const: IsConst<N>) -> IsConst<Inc<N>> {
    app_is_const(succ_is_const(), n_is_const)
}

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
/// `is_const(add)`.
pub fn add_is_const() -> IsConst<Add> {unimplemented!()}
/// `(n : nat)  =>  add(0, n) = n`.
pub fn add_zero<N: Prop>(_n_ty: Ty<N, Nat>) -> Eq<Plus<Zero, N>, N> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat)  =>  add(succ(n), m) = succ(add(n, m))`.
pub fn add_succ<N: Prop, M: Prop>(
    _ty_n: Ty<N, Nat>,
    _ty_m: Ty<M, Nat>
) -> Eq<Plus<Inc<N>, M>, Inc<Plus<N, M>>> {unimplemented!()}
/// `(n : nat)  =>  succ(n) == n + 1`.
pub fn add_succ_plus_one<N: Prop>(_ty_n: Ty<N, Nat>) -> Eq<Inc<N>, Plus<N, One>> {unimplemented!()}
/// `(n : nat)  =>  add(n, 0) == n`.
pub fn add_zero_right<N: Prop>(_ty_n: Ty<N, Nat>) -> Eq<Plus<N, Zero>, N> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (n + a == m + a)  =>  (n == m)`.
pub fn add_rev_eq_left<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Plus<N, A>, Plus<M, A>>
) -> Eq<N, M> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (n + a == m + a)  =>  (n == m)`.
pub fn add_rev_eq_right<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Plus<A, N>, Plus<A, M>>
) -> Eq<N, M> {unimplemented!()}

/// `1 : nat`.
pub fn one_ty() -> Ty<One, Nat> {app_fun_ty(succ_ty(), zero_ty())}
/// `2 : nat`.
pub fn two_ty() -> Ty<Two, Nat> {app_fun_ty(succ_ty(), one_ty())}
/// `1 + 1 == 2`.
pub fn eq_plus_one_one_two() -> Eq<Plus<One, One>, Two> {
    eq::transitivity(add_succ(zero_ty(), one_ty()), app_eq(add_zero(one_ty())))
}
/// `(a == b)  =>  (a + c == b + c)`.
pub fn add_eq_left<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Plus<A, C>, Plus<B, C>> {
    app_eq(tup_eq_fst(x))
}
/// `(a == b)  =>  (c + a == c + b)`.
pub fn add_eq_right<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Plus<C, A>, Plus<C, B>> {
    app_eq(tup_eq_snd(x))
}
/// `(n == 0)  =>  (n + 0 == n)`.
pub fn add_eq_zero_to_add_zero_right<N: Prop>(eq_n_zero: Eq<N, Zero>) -> Eq<Plus<N, Zero>, N> {
    eq::transitivity(eq::transitivity(add_eq_left(eq_n_zero.clone()),
        add_zero(zero_ty())), eq::symmetry(eq_n_zero))
}
/// `is_const(k)  =>  ((n + k)[n := m]  ==  m + k)`.
pub fn add_subst_const_right<N: Prop, M: Prop, K: Prop>(
    k_is_const: IsConst<K>
) -> Eq<Subst<Plus<N, K>, N, M>, Plus<M, K>> {
    eq::transitivity(eq::transitivity(subst_app(), app_map_eq(subst_const(add_is_const()))),
        app_eq(eq::transitivity(eq::transitivity(subst_tup(),
        tup_eq_snd(subst_const(k_is_const))), tup_eq_fst(subst_trivial()))))
}
