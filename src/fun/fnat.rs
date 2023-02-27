//! Natural numbers.

use super::*;
use bool_alg::{Bool, Fa, FNot, Tr};

/// The type of natural numbers.
#[derive(Copy, Clone)]
pub struct Nat(());

/// `n == 0`.
pub type IsZero<N> = Eq<N, Zero>;

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
/// `(x : nat)  =>  (x == 0) ⋁ ((prev(x) : nat) ⋀ (x == succ(prev(x)))`.
pub fn nat_def<X: Prop>(
    _x_ty: Ty<X, Nat>
) -> Or<IsZero<X>, And<Ty<Prev<X>, Nat>, Eq<X, Succ<Prev<X>>>>> {unimplemented!()}
/// `(n : nat) ⋀ (n == succ(n))  =>  false`.
pub fn para_eq_succ<N: Prop>(_: And<Ty<N, Nat>, Eq<N, Succ<N>>>) -> False {unimplemented!()}
/// `0 == succ(n)  =>  false`.
pub fn para_pre_zero<N: Prop>(_: IsZero<Succ<N>>) -> False {unimplemented!()}
/// `succ(n) == succ(m)  =>  n == m`.
pub fn succ_eq_rev<N: Prop, M: Prop>(_: Eq<Succ<N>, Succ<M>>) -> Eq<N, M> {unimplemented!()}
/// Induction on natural numbers.
///
/// ```text
/// (p : nat -> bool) ⋀
/// (p(0) == tr)^true ⋀
/// (p(succ(n)) == tr)^(succ(n) : nat)
/// ----------------------------------
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
/// p(succ(n))^(succ(n) : nat)
/// --------------------------
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
/// `f : nat -> a ⋀ g : nat -> a ⋀
/// (f(0) == g(0))^true ⋀ (f(succ(n)) == g(succ(n)))^(succ(n) : nat)  =>  (f == g)`.
pub fn nat1_fun_ext<N: VProp, F: Prop, G: Prop, A: Prop>(
    ty_f: Ty<F, Pow<A, Nat>>,
    ty_g: Ty<G, Pow<A, Nat>>,
    case_zero: Tauto<Eq<App<F, Zero>, App<G, Zero>>>,
    case_succ: Pow<Eq<App<F, Succ<N>>, App<G, Succ<N>>>, Ty<Succ<N>, Nat>>
) -> Eq<F, G> {
    nat_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_zero)),
               app_fun_ext(ty_f, ty_g, case_succ))
}
/// `succ(n) : nat  =>  n == prev(succ(n))`.
pub fn previous<N: Prop>(x: Ty<Succ<N>, Nat>) -> Eq<N, Prev<Succ<N>>> {
    match nat_def(x) {
        Left(y) => imply::absurd()(para_pre_zero(y)),
        Right(y) => succ_eq_rev(y.1),
    }
}
/// `(a : nat) ⋀ x^(a == 0) ⋀ x^(a == succ(prev(a))  =>  x`.
pub fn nat_cover<A: Prop, X: Prop>(
    ty_a: Ty<A, Nat>,
    pow_x_eq_a_zero: Pow<X, IsZero<A>>,
    y: Pow<X, Eq<A, Succ<Prev<A>>>>
) -> X {
    fn f<A: Prop>(ty_a: Ty<A, Nat>) -> Or<IsZero<A>, Eq<A, Succ<Prev<A>>>> {
        match nat_def(ty_a) {
            Left(x) => Left(x),
            Right((_, x)) => Right(x),
        }
    }
    cover(ty_a, f, pow_x_eq_a_zero, y)
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
pub fn succ_app_is_const<N: Prop>(n_is_const: IsConst<N>) -> IsConst<Succ<N>> {
    app_is_const(succ_is_const(), n_is_const)
}
/// `n : nat  =>  succ(n) : nat`.
pub fn succ_app_ty<N: Prop>(ty_n: Ty<N, Nat>) -> Ty<Succ<N>, Nat> {app_fun_ty(succ_ty(), ty_n)}
/// `succ(n) : nat  =>  n : nat`.
pub fn succ_rev_app_ty<N: Prop>(ty_succ_n: Ty<Succ<N>, Nat>) -> Ty<N, Nat> {
    match nat_def(ty_succ_n) {
        Left(eq_succ_n_zero) => imply::absurd()(para_pre_zero(eq_succ_n_zero)),
        Right(x) => path_semantics::ty_in_left_arg(x.0, eq::symmetry(succ_eq_rev(x.1))),
    }
}
/// `(a == b)  =>  (succ(a) == succ(b))`.
pub fn succ_eq<A: Prop, B: Prop>(x: Eq<A, B>) -> Eq<Succ<A>, Succ<B>> {app_eq(x)}

/// Apply successor to argument `succ(n)`.
pub type Succ<N> = App<FSucc, N>;
/// One `1 := succ(0)`.
pub type One = Succ<Zero>;
/// Two `2 := succ(1)`.
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
/// `(succ(n) : nat) ⋀ (m : nat)  =>  add(succ(n), m) = succ(add(n, m))`.
pub fn add_succ<N: Prop, M: Prop>(
    _ty_succ_n: Ty<Succ<N>, Nat>,
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
    eq::transitivity(add_succ(one_ty(), one_ty()), app_eq(add_zero(one_ty())))
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
pub fn add_eq_zero_to_add_zero_right<N: Prop>(eq_n_zero: IsZero<N>) -> Eq<Add<N, Zero>, N> {
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
        add_succ(one_ty(), ty_n.clone()), add_symmetry()
    ), app_eq(add_symmetry())), app_eq(add_zero_right(ty_n.clone()))))
}

/// Multiplication.
#[derive(Copy, Clone)]
pub struct FMul(());

/// `a * b`.
pub type Mul<A, B> = App<FMul, Tup<A, B>>;

/// `mul : (nat, nat) -> nat`.
pub fn mul_ty() -> Ty<FMul, Pow<Nat, Tup<Nat, Nat>>> {unimplemented!()}
/// `is_const(mul)`.
pub fn mul_is_const() -> IsConst<FMul> {unimplemented!()}
/// `(n : nat)  =>  mul(0, n) = 0`.
pub fn mul_zero<N: Prop>(_ty_n: Ty<N, Nat>) -> IsZero<Mul<Zero, N>> {unimplemented!()}
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
/// `mul(a, add(b, c)) == add(mul(a, b), mul(a, c))`.
pub fn mul_distr<A: Prop, B: Prop, C: Prop>() -> Eq<Mul<A, Add<A, B>>, Add<Mul<A, B>, Add<B, C>>> {
    unimplemented!()
}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (n * a == m * a) ⋀ ¬(a == 0)  =>  (n == m)`.
pub fn mul_rev_eq_left<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Mul<N, A>, Mul<M, A>>,
    _neq_a_zero: Not<IsZero<A>>,
) -> Eq<N, M> {unimplemented!()}
/// `(n : nat) ⋀ (m : nat) ⋀ (a : nat) ⋀ (a * n == a * m) ⋀ ¬(a == 0)  =>  (n == m)`.
pub fn mul_rev_eq_right<N: Prop, M: Prop, A: Prop>(
    _n_ty: Ty<N, Nat>,
    _m_ty: Ty<M, Nat>,
    _a_ty: Ty<A, Nat>,
    _x: Eq<Mul<A, N>, Mul<A, M>>,
    _neq_a_zero: Not<IsZero<A>>,
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

/// Even.
#[derive(Copy, Clone)]
pub struct FEven(());

/// `even(a)`.
pub type Even<A> = App<FEven, A>;

/// `even : nat -> bool`.
pub fn even_ty() -> Ty<FEven, Pow<Bool, Nat>> {unimplemented!()}
/// `even(0) = tr`.
pub fn even_zero() -> Eq<Even<Zero>, Tr> {unimplemented!()}
/// `n : nat  =>  even(succ(n)) = not(even(n))`.
pub fn even_succ<N: Prop>(_ty_n: Ty<N, Nat>) -> Eq<Even<Succ<N>>, App<FNot, Even<N>>> {
    unimplemented!()
}

/// `n : nat  =>  even(succ(succ(n))) == even(n)`.
pub fn eq_even_succ_succ<N: Prop>(ty_n: Ty<N, Nat>) -> Eq<Even<Succ<Succ<N>>>, Even<N>> {
    eq::transitivity(even_succ(succ_app_ty(ty_n.clone())),
        eq::transitivity(app_eq(even_succ(ty_n.clone())),
        bool_alg::eq_not_not(app_fun_ty(even_ty(), ty_n))))
}
/// `even . (succ . succ) == even`.
pub fn eq_comp_even_succ_succ_proof<N: VProp>() -> Eq<Comp<FEven, Comp<FSucc, FSucc>>, FEven> {
    fn f<N: Prop>(x: Eq<Even<Succ<Succ<N>>>, Even<N>>) ->
    Eq<App<Comp<FEven, Comp<FSucc, FSucc>>, N>, Even<N>> {
        eq::in_left_arg(x, eq::transitivity(app_eq(eq_app_comp()), eq_app_comp()))
    }
    nat1_fun_ext(
        comp_ty(comp_ty(succ_ty(), succ_ty()), even_ty()),
        even_ty(),
        hooo::pow_transitivity(tauto!(eq_even_succ_succ(zero_ty())), f),
        hooo::pow_transitivity(eq_even_succ_succ::<Succ<N>>, f),
    )
}
/// `even . (succ . succ) == even`.
///
/// This is the same as `eq_comp_even_succ_succ_proof` but without variable argument.
pub fn eq_comp_even_succ_succ() -> Eq<Comp<FEven, Comp<FSucc, FSucc>>, FEven> {
    unimplemented!()
}

/// Odd.
#[derive(Copy, Clone)]
pub struct FOdd(pub Comp<FNot, FEven>);

/// `odd(a)`.
pub type Odd<A> = App<FOdd, A>;

/// `odd  ==  not . even`.
pub fn odd_def() -> Eq<FOdd, Comp<FNot, FEven>> {eqx!(def FOdd)}
/// `odd : nat -> bool`.
pub fn odd_ty() -> Ty<FOdd, Pow<Bool, Nat>> {
    eqx!(comp_ty(even_ty(), bool_alg::not_ty()), odd_def, tyl)
}
/// `odd(0) = fa`.
pub fn odd_zero() -> Eq<Odd<Zero>, Fa> {comp_app_def(even_zero(), bool_alg::not_tr(), odd_def())}
/// `n : nat  =>  odd(succ(n)) = not(odd(n))`.
pub fn odd_succ<N: Prop>(ty_n: Ty<N, Nat>) -> Eq<Odd<Succ<N>>, App<FNot, Odd<N>>> {
    use eq::transitivity as trans;

    trans(app_map_eq(odd_def()), trans(trans(trans(eq::symmetry(eq_app_comp()),
        app_eq(even_succ(ty_n))), app_eq(eq_app_comp())),
        app_eq(app_map_eq(eq::symmetry(odd_def())))))
}
/// `(n : nat) ⋀ (even(n) == odd(n))  =>  false`.
pub fn para_eq_even_odd<N: Prop>(ty_n: Ty<N, Nat>, x: Eq<Even<N>, Odd<N>>) -> False {
    let y = eq::trans3(x, app_map_eq(odd_def()), eq::symmetry(eq_app_comp()));
    bool_alg::para_eq_tr_fa(match bool_alg::bool_values(app_fun_ty(even_ty(), ty_n)) {
        Left(eq_even_n_tr) => eq::in_left_arg(eq::trans3(y, app_eq(eq_even_n_tr.clone()),
            bool_alg::not_tr()), eq_even_n_tr),
        Right(eq_even_n_fa) => eq::in_left_arg(eq_even_n_fa.clone(), eq::trans3(y,
            app_eq(eq_even_n_fa), bool_alg::not_fa())),
    })
}
