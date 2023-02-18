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
/// `(x : nat)  =>  (x == 0) ⋁ (prev(x) : nat ⋀ x == succ(prev(x))`.
pub fn nat_def<X: Prop>(
    _x_ty: Ty<X, Nat>
) -> Either<Eq<X, Zero>, And<Ty<Prev<X>, Nat>, Eq<X, Succ<Prev<X>>>>> {unimplemented!()}
/// `(n : nat) ⋀ (n == succ(n))  =>  false`.
pub fn para_eq_succ<N: Prop>(_: And<Ty<N, Nat>, Eq<N, Succ<N>>>) -> False {unimplemented!()}
/// `0 == succ(n)  =>  false`.
pub fn para_pre_zero<N: Prop>(_: Eq<Zero, Succ<N>>) -> False {unimplemented!()}
/// `succ(n) == succ(m)  =>  n == m`.
pub fn inc_eq_rev<N: Prop, M: Prop>(_: Eq<Succ<N>, Succ<M>>) -> Eq<N, M> {unimplemented!()}
/// Induction on natural numbers.
///
/// ```text
/// (p : nat -> bool) ⋀
/// (p(0) == tr)^true ⋀
/// (p(succ(n)) == tr)^(n : nat)
/// ----------------------------
/// (p(n) == tr)^(n : nat)
/// ```
pub fn induction<N: VProp, P: Prop>(
    _ty_p: Ty<P, Pow<Bool, Nat>>,
    _case_zero: Tauto<Eq<App<P, Zero>, Tr>>,
    _case_n: Pow<Eq<App<P, Succ<N>>, Tr>, Ty<Succ<N>, Nat>>,
) -> Pow<Eq<App<P, N>, True>, Ty<N, Nat>> {unimplemented!()}
/// Type induction on natural numbers.
///
/// ```text
/// (p : nat -> type(0)) ⋀
/// p(0)^true ⋀
/// p(succ(n))^(n : nat)
/// ----------------------------
/// p(n)^(n : nat)
/// ```
pub fn induction_ty<N: VProp, P: Prop, L: nat::Nat>(
    _ty_p: Ty<P, Pow<Type<L>, Nat>>,
    _case_zero: Tauto<App<P, Zero>>,
    _case_n: Pow<App<P, Succ<N>>, Ty<Succ<N>, Nat>>,
) -> Pow<App<P, N>, Ty<N, Nat>> {unimplemented!()}
/// `x^(n : nat)  =>  (x[n := succ(n)])^(succ(n) : nat)`.
pub fn subst_induction<N: Prop, X: Prop, M: Prop>(
    _: Pow<X, Ty<N, Nat>>
) -> Pow<Subst<X, N, Succ<N>>, Ty<Succ<N>, Nat>> {unimplemented!()}
/// `∃ 0 : nat { x } ⋀ ∃ succ(n) : nat { x }  =>  x`.
pub fn nat_exists<N: VProp, X: Prop>(
    _exists_zero_x: Exists<Ty<Zero, Nat>, X>,
    _exists_succ_n_x: Exists<Ty<Succ<N>, Nat>, X>
) -> X {unimplemented!()}
/// `n : nat  =>  succ(prev(n)) == prev(succ(n))`.
pub fn previous_symmetry<N: Prop>(_ty_n: Ty<N, Nat>) -> Eq<Succ<Prev<N>>, Prev<Succ<N>>> {
    unimplemented!()
}

/// `succ(n)[n := a]  ==  succ(a)`.
pub fn subst_succ<N: Prop, A: Prop>() -> Eq<Subst<Succ<N>, N, A>, Succ<A>> {
    eq::transitivity(eq::transitivity(subst_app(), app_map_eq(subst_const(succ_is_const()))),
        app_eq(subst_trivial()))
}
/// `(0 == 1)  =>  false`.
pub fn para_eq_zero_one(x: Eq<Zero, One>) -> False {para_eq_succ((zero_ty(), x))}
/// `f : nat -> nat ⋀ g : nat -> nat ⋀
/// (f(0) == g(0))^true ⋀ (f(succ(n)) == g(succ(n)))^(succ(n) : nat)  =>  (f == g)`.
pub fn nat1_fun_ext<N: VProp, F: Prop, G: Prop>(
    ty_f: Ty<F, Pow<Nat, Nat>>,
    ty_g: Ty<G, Pow<Nat, Nat>>,
    case_zero: Tauto<Eq<App<F, Zero>, App<G, Zero>>>,
    case_succ: Pow<Eq<App<F, Succ<N>>, App<G, Succ<N>>>, Ty<Succ<N>, Nat>>
) -> Eq<F, G> {
    nat_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_zero)),
               app_fun_ext(ty_f, ty_g, case_succ))
}
/// `succ(n) : nat  =>  n == prev(succ(n))`.
pub fn previous<N: Prop>(x: Ty<Succ<N>, Nat>) -> Eq<N, Prev<Succ<N>>> {
    match nat_def(x) {
        Left(y) => imply::absurd()(para_pre_zero(eq::symmetry(y))),
        Right(y) => inc_eq_rev(y.1),
    }
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
pub struct FSucc(());

/// `succ : nat -> nat`.
pub fn succ_ty() -> Ty<FSucc, Pow<Nat, Nat>> {unimplemented!()}
/// `is_const(succ)`.
pub fn succ_is_const() -> IsConst<FSucc> {unimplemented!()}

/// `is_const(n)  =>  is_const(succ(n))`.
pub fn inc_is_const<N: Prop>(n_is_const: IsConst<N>) -> IsConst<Succ<N>> {
    app_is_const(succ_is_const(), n_is_const)
}
/// `succ(n) : nat  =>  n : nat`.
pub fn succ_rev_ty<N: Prop>(ty_succ_n: Ty<Succ<N>, Nat>) -> Ty<N, Nat> {
    match nat_def(ty_succ_n) {
        Left(eq_succ_n_zero) => imply::absurd()(para_pre_zero(eq::symmetry(eq_succ_n_zero))),
        Right(x) => path_semantics::ty_in_left_arg(x.0, eq::symmetry(inc_eq_rev(x.1))),
    }
}

/// Apply successor to argument.
pub type Succ<N> = App<FSucc, N>;
/// One.
pub type One = Succ<Zero>;
/// Two.
pub type Two = Succ<One>;

/// Addition.
#[derive(Copy, Clone)]
pub struct FAdd(());

/// `a + b`.
pub type Add<A, B> = App<FAdd, Tup<A, B>>;

/// `add : (nat, nat) -> nat`.
pub fn add_ty() -> Ty<FAdd, Pow<Nat, Tup<Nat, Nat>>> {unimplemented!()}
/// `is_const(add)`.
pub fn add_is_const() -> IsConst<FAdd> {unimplemented!()}
/// `(n : nat)  =>  add(0, n) = n`.
pub fn add_zero<N: Prop>(_n_ty: Ty<N, Nat>) -> Eq<Add<Zero, N>, N> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat)  =>  add(succ(n), m) = succ(add(n, m))`.
pub fn add_succ<N: Prop, M: Prop>(
    _ty_n: Ty<N, Nat>,
    _ty_m: Ty<M, Nat>
) -> Eq<Add<Succ<N>, M>, Succ<Add<N, M>>> {unimplemented!()}
/// `add(n, m) == add(m, n)`.
pub fn add_symmetry<N: Prop, M: Prop>() -> Eq<Add<N, M>, Add<M, N>> {unimplemented!()}
/// `add(add(a, b), c) == add(a, add(b, c))`.
pub fn add_assoc<A: Prop, B: Prop, C: Prop>() -> Eq<Add<Add<A, B>, C>, Add<A, Add<B, C>>> {
    unimplemented!()
}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (n + a == m + a)  =>  (n == m)`.
pub fn add_rev_eq_left<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Add<N, A>, Add<M, A>>
) -> Eq<N, M> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (a + n == a + m)  =>  (n == m)`.
pub fn add_rev_eq_right<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Add<A, N>, Add<A, M>>
) -> Eq<N, M> {unimplemented!()}

/// `1 : nat`.
pub fn one_ty() -> Ty<One, Nat> {app_fun_ty(succ_ty(), zero_ty())}
/// `2 : nat`.
pub fn two_ty() -> Ty<Two, Nat> {app_fun_ty(succ_ty(), one_ty())}
/// `1 + 1 == 2`.
pub fn eq_plus_one_one_two() -> Eq<Add<One, One>, Two> {
    eq::transitivity(add_succ(zero_ty(), one_ty()), app_eq(add_zero(one_ty())))
}
/// `(n : nat)  =>  add(n, 0) == n`.
pub fn add_zero_right<N: Prop>(ty_n: Ty<N, Nat>) -> Eq<Add<N, Zero>, N> {
    eq::in_left_arg(add_zero(ty_n), add_symmetry())
}
/// `(a == b)  =>  (a + c == b + c)`.
pub fn add_eq_left<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Add<A, C>, Add<B, C>> {
    app_eq(tup_eq_fst(x))
}
/// `(a == b)  =>  (c + a == c + b)`.
pub fn add_eq_right<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Add<C, A>, Add<C, B>> {
    app_eq(tup_eq_snd(x))
}
/// `(n == 0)  =>  (n + 0 == n)`.
pub fn add_eq_zero_to_add_zero_right<N: Prop>(eq_n_zero: Eq<N, Zero>) -> Eq<Add<N, Zero>, N> {
    eq::transitivity(eq::transitivity(add_eq_left(eq_n_zero.clone()),
        add_zero(zero_ty())), eq::symmetry(eq_n_zero))
}
/// `is_const(k)  =>  ((n + k)[n := m]  ==  m + k)`.
pub fn add_subst_const_right<N: Prop, M: Prop, K: Prop>(
    k_is_const: IsConst<K>
) -> Eq<Subst<Add<N, K>, N, M>, Add<M, K>> {
    eq::transitivity(eq::transitivity(subst_app(), app_map_eq(subst_const(add_is_const()))),
        app_eq(eq::transitivity(eq::transitivity(subst_tup(),
        tup_eq_snd(subst_const(k_is_const))), tup_eq_fst(subst_trivial()))))
}
/// `(n : nat)  =>  succ(n) == n + 1`.
pub fn add_succ_plus_one<N: Prop>(ty_n: Ty<N, Nat>) -> Eq<Succ<N>, Add<N, One>> {
    eq::symmetry(eq::in_right_arg(eq::in_right_arg(eq::in_left_arg(
        add_succ(zero_ty(), ty_n.clone()), add_symmetry()
    ), app_eq(add_symmetry())), app_eq(add_zero_right(ty_n.clone()))))
}

/// Multiplication.
#[derive(Copy, Clone)]
pub struct Multiply(());

/// `a * b`.
pub type Mul<A, B> = App<Multiply, Tup<A, B>>;

/// `mul : (nat, nat) -> nat`.
pub fn mul_ty() -> Ty<Multiply, Pow<Nat, Tup<Nat, Nat>>> {unimplemented!()}
/// `is_const(mul)`.
pub fn mul_is_const() -> IsConst<Multiply> {unimplemented!()}
/// `(n : nat)  =>  mul(0, n) = 0`.
pub fn mul_zero<N: Prop>(_ty_n: Ty<N, Nat>) -> Eq<Mul<Zero, N>, Zero> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat)  =>  mul(succ(n), m) == add(m, mul(n, m))`.
pub fn mul_succ<N: Prop, M: Prop>(
    _ty_n: Ty<N, Nat>,
    _ty_m: Ty<M, Nat>
) -> Eq<Mul<Succ<N>, M>, Add<M, Mul<N, M>>> {unimplemented!()}
/// `mul(n, m) == mul(m, n)`.
pub fn mul_symmetry<N: Prop, M: Prop>() -> Eq<Mul<N, M>, Mul<M, N>> {unimplemented!()}
/// `mul(mul(a, b), c) == mul(a, mul(b, c))`.
pub fn mul_assoc<A: Prop, B: Prop, C: Prop>() -> Eq<Mul<Mul<A, B>, C>, Mul<A, Mul<B, C>>> {
    unimplemented!()
}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (n * a == m * a) ⋀ ¬(a == 0)  =>  (n == m)`.
pub fn mul_rev_eq_left<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Mul<N, A>, Mul<M, A>>,
    _neq_a_zero: Not<Eq<A, Zero>>,
) -> Eq<N, M> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (a * n == a * m) ⋀ ¬(a == 0)  =>  (n == m)`.
pub fn mul_rev_eq_right<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Mul<A, N>, Mul<A, M>>,
    _neq_a_zero: Not<Eq<A, Zero>>,
) -> Eq<N, M> {unimplemented!()}

/// `(n : nat)  =>  mul(1, n) = n`.
pub fn mul_one<N: Prop>(ty_n: Ty<N, Nat>) -> Eq<Mul<One, N>, N> {
    eq::transitivity(eq::transitivity(mul_succ(zero_ty(), ty_n.clone()),
        add_eq_right(mul_zero(ty_n.clone()))), eq::in_left_arg(add_zero(ty_n), add_symmetry()))
}
/// `(a == b)  =>  (a + c == b + c)`.
pub fn mul_eq_left<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Mul<A, C>, Mul<B, C>> {
    app_eq(tup_eq_fst(x))
}
/// `(a == b)  =>  (c + a == c + b)`.
pub fn mul_eq_right<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Mul<C, A>, Mul<C, B>> {
    app_eq(tup_eq_snd(x))
}
