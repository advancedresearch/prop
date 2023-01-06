//! # Path Semantics
//!
//! Path Semantics has a core axiom which is used to model mathematics.
//!
//! This core axiom is modelled here,
//! lifting proof of path semantical order to expressions of propositions.
//!
//! For more information, see
//! https://github.com/advancedresearch/path_semantics.

#![allow(unreachable_code)]

use crate::*;

pub use quality::Q;
pub use quality::EqQ;
pub use quality::left as refl_left;
pub use quality::right as refl_right;

pub use lprop::*;
pub use pord::*;
pub use ty::*;

use qubit::Qu;
use existence::EProp;
use univalence::Hom;
use nat::*;

mod lprop;
mod pord;
mod ty;

/// `true == ltrue`.
pub fn eq_true_ltrue<N: Nat>() -> Eq<True, LTrue<N>> {
    (LTrue(Default::default()).map_any(), True.map_any())
}

/// `true ~~ x`.
#[cfg(feature = "old_homotopy_levels")]
pub fn q_true<X: LProp>() -> Q<True, X> where X::N: Nat {
    univalence::h0_q_true(ty_true())
}

/// `x ~~ x`.
#[cfg(feature = "old_homotopy_levels")]
pub fn true_q<X: LProp>() -> Q<X, X> where X::N: Nat {
    univalence::h0_true_q(ty_true())
}

/// `x`.
#[cfg(feature = "old_homotopy_levels")]
pub fn lproof<X: LProp>() -> X where X::N: Nat {
    let q_true_x = q_true();
    quality::to_eq(q_true_x).0(True)
}

/// `(x ~~ x) == x`.
#[cfg(feature = "old_homotopy_levels")]
pub fn lim<X: LProp>() -> Eq<Q<X, X>, X> where X::N: Nat {
    univalence::h0_lim(ty_true())
}

/// `(x ~~ x) ~~ x`.
#[cfg(feature = "old_homotopy_levels")]
pub fn qlim<X: LProp>() -> Q<Q<X, X>, X> where X::N: Nat {
    univalence::h0_qlim(ty_true())
}

/// Core axiom of Path Semantics.
pub type PSem<F1, F2, X1, X2> = Imply<
    And<And<Q<F1, F2>, And<POrdProof<F1, X1>, POrdProof<F2, X2>>>,
        And<Imply<F1, X1>, Imply<F2, X2>>>,
    Q<X1, X2>,
>;

/// Naive axiom of Path Semantics (without order assumption).
pub type PSemNaive<F1, F2, X1, X2> = Imply<
    And<Q<F1, F2>, And<Imply<F1, X1>, Imply<F2, X2>>>,
    Q<X1, X2>
>;

/// Sends first argument of Logical AND to higher level.
pub type PAndFst<A, B, C, D> = Imply<
    And<Q<And<A, B>, C>, Imply<C, D>>,
    Q<A, D>,
>;
/// Sends second argument of Logical AND to higher level.
pub type PAndSnd<A, B, C, D> = Imply<
    And<Q<And<A, B>, C>, Imply<C, D>>,
    Q<B, D>,
>;

/// Sends first argument of Logical OR to higher level.
pub type POrFst<A, B, C, D> = Imply<
    And<Q<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<B>, Q<A, D>>
>;

/// Sends second argument of Logical OR to higher level.
pub type POrSnd<A, B, C, D> = Imply<
    And<Q<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<A>, Q<B, D>>
>;

/// Normalised naive core axiom.
pub type PSemNaiveNorm<A, B, C, D> = PSemNaive<
    LN<Zero, A, B, C, D>,
    LN<One, A, B, C, D>,
    LN<Two, A, B, C, D>,
    LN<Three, A, B, C, D>
>;

/// Assumes the core axiom safely for propositions.
pub fn assume<A: Prop, B: Prop, C: Prop, D: Prop>() -> PSem<A, B, C, D> {
    unimplemented!()
}

/// Converts to naive core axiom.
pub fn to_naive<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSem<A, B, C, D>
) -> PSemNaive<A, B, C, D>
    where A: POrd<C>, B: POrd<D>
{
    Rc::new(move |(f, (g, h))| p.clone()(((f, (POrdProof::new(), POrdProof::new())), (g, h))))
}

/// Assume naive core axiom safely.
pub fn assume_naive<A: Prop, B: Prop, C: Prop, D: Prop>() -> PSemNaive<A, B, C, D>
    where A: POrd<C>, B: POrd<D>
{
    to_naive(assume())
}

/// Generates naive core axiom at increased path semantical proposition level.
pub fn assume_inc_path_level<N: Nat, A: LProp, B: LProp, C: LProp, D: LProp>()
-> PSemNaive<IncLevel<A, N>, IncLevel<B, N>, IncLevel<C, N>, IncLevel<D, N>>
    where <IncLevel<A, N> as LProp>::N: Lt<<IncLevel<C, N> as LProp>::N>,
          <IncLevel<B, N> as LProp>::N: Lt<<IncLevel<D, N> as LProp>::N>,
          (A::N, N): Add,
          (B::N, N): Add,
          (C::N, N): Add,
          (D::N, N): Add,
{
    assume_naive()
}

/// Assume a normalised naive core axiom.
///
/// The orientation is detected automatically and restored to a naive core axiom
/// which has a proof to any valid order.
pub fn assume_norm_path_level<A: LProp, B: LProp, C: LProp, D: LProp>()
-> PSemNaiveNorm<A, B, C, D>
    where
        (A::N, B::N): SortMin<A, B> + SortMax<A, B>,
        (C::N, D::N): SortMin<C, D> + SortMax<C, D>,
        (<Min<A, B> as LProp>::N, <Min<C, D> as LProp>::N):
            SortMin<Min<A, B>, Min<C, D>> +
            SortMax<Min<A, B>, Min<C, D>>,
        (<Max<A, B> as LProp>::N, <Max<C, D> as LProp>::N):
            SortMin<Max<A, B>, Max<C, D>> +
            SortMax<Max<A, B>, Max<C, D>>,
        (<MaxMin<A, B, C, D> as LProp>::N, <MinMax<A, B, C, D> as LProp>::N):
            SortMin<MaxMin<A, B, C, D>, MinMax<A, B, C, D>> +
            SortMax<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>,
        <MinMin<A, B, C, D> as LProp>::N:
            Lt<<Maxi<A, B, C, D> as LProp>::N>,
        <Mixi<A, B, C, D> as LProp>::N:
            Lt<<MaxMax<A, B, C, D> as LProp>::N>,
{
    assume_naive()
}

/// Generates a naive core axiom which has reflection as end-lines.
pub fn assume_refl<A: Prop, B: Prop>() -> PSemNaive<A, A, B, B>
    where A: POrd<B>
{
    assume_naive()
}

/// Reduce naive core axiom in case of false to equality of associated propositions.
pub fn naive_red_false<A: Prop, B: Prop>(
    p: PSemNaive<False, False, A, B>,
    q: Q<False, False>,
) -> Q<A, B> {
    p((q, (imply::absurd(), imply::absurd())))
}

/// Composition.
pub fn comp<F1: Prop, F2: Prop, F3: Prop, F4: Prop, X1: Prop, X2: Prop>(
    f: PSem<F1, F2, F3, F4>,
    g: PSem<F3, F4, X1, X2>,
    pr_f1_f3: POrdProof<F1, F3>,
    pr_f2_f4: POrdProof<F2, F4>,
    pr_f3_x1: POrdProof<F3, X1>,
    pr_f4_x2: POrdProof<F4, X2>,
    f1_f3: Imply<F1, F3>,
    f2_f4: Imply<F2, F4>,
    f3_x1: Imply<F3, X1>,
    f4_x2: Imply<F4, X2>,
) -> PSem<F1, F2, X1, X2> {
    Rc::new(move |((f1_eq_f2, (_pr_f1_x1, _pr_f2_x2)), (_f1_x1, _f2_x2))| {
        let f3_eq_f4 = f(((f1_eq_f2, (pr_f1_f3.clone(), pr_f2_f4.clone())), (f1_f3.clone(), f2_f4.clone())));
        let x1_eq_x2 = g(((f3_eq_f4, (pr_f3_x1.clone(), pr_f4_x2.clone())), (f3_x1.clone(), f4_x2.clone())));
        x1_eq_x2
    })
}

/// Composition using the naive core axiom.
pub fn naive_comp<F1: Prop, F2: Prop, F3: Prop, F4: Prop, X1: Prop, X2: Prop>(
    f: PSemNaive<F1, F2, F3, F4>,
    g: PSemNaive<F3, F4, X1, X2>,
    f1_f3: Imply<F1, F3>,
    f2_f4: Imply<F2, F4>,
    f3_x1: Imply<F3, X1>,
    f4_x2: Imply<F4, X2>,
) -> PSemNaive<F1, F2, X1, X2> {
    Rc::new(move |(f1_eq_f2, (_f1_x1, _f2_x2))| {
        let f3_eq_f4 = f((f1_eq_f2, (f1_f3.clone(), f2_f4.clone())));
        let x1_eq_x2 = g((f3_eq_f4, (f3_x1.clone(), f4_x2.clone())));
        x1_eq_x2
    })
}

/// Constructs a 2D naive core axiom from two naive core axioms,
/// where one is normalised of the other.
pub fn xy_norm<
    A: LProp,
    B: LProp,
    C: LProp,
    D: LProp,
>(
    p1: PSemNaive<A, B, C, D>,
    p2: PSemNaiveNorm<A, B, C, D>,
    f_eq_a_b: Imply<Q<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>>,
                And<Q<A, B>, Q<LN<Zero, A, B, C, D>, LN<One, A, B, C, D>>>>,
    f_a_c: Imply<Imply<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>>,
                 And<Imply<A, C>, Imply<LN<Zero, A, B, C, D>, LN<Two, A, B, C, D>>>>,
    f_b_d: Imply<Imply<B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>,
                       D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>>,
                 And<Imply<B, D>, Imply<LN<One, A, B, C, D>, LN<Three, A, B, C, D>>>>,
    f_eq_c_d: Imply<And<Q<C, D>, Q<LN<Two, A, B, C, D>, LN<Three, A, B, C, D>>>,
                    Q<C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>,
                       D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>>>
) -> PSemNaive<
        A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
        B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>,
        C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>,
        D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>,
>
    where
        // Normalisation requirements.
        (A::N, B::N): SortMin<A, B> + SortMax<A, B>,
        (C::N, D::N): SortMin<C, D> + SortMax<C, D>,
        (<Min<A, B> as LProp>::N, <Min<C, D> as LProp>::N):
            SortMin<Min<A, B>, Min<C, D>> +
            SortMax<Min<A, B>, Min<C, D>>,
        (<Max<A, B> as LProp>::N, <Max<C, D> as LProp>::N):
            SortMin<Max<A, B>, Max<C, D>> +
            SortMax<Max<A, B>, Max<C, D>>,
        (<MaxMin<A, B, C, D> as LProp>::N, <MinMax<A, B, C, D> as LProp>::N):
            SortMin<MaxMin<A, B, C, D>, MinMax<A, B, C, D>> +
            SortMax<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>,
        <MinMin<A, B, C, D> as LProp>::N:
            Lt<<Maxi<A, B, C, D> as LProp>::N>,
        <Mixi<A, B, C, D> as LProp>::N:
            Lt<<MaxMax<A, B, C, D> as LProp>::N>,
{
    Rc::new(move |(eq_a_b, (a_c, b_d))| {
        let (p1_eq_a_b, p2_eq_a_b) = f_eq_a_b.clone()(eq_a_b);
        let (p1_a_c, p2_a_c) = f_a_c.clone()(a_c);
        let (p1_b_d, p2_b_d) = f_b_d.clone()(b_d);
        let p1_eq_c_d = p1.clone()((p1_eq_a_b, (p1_a_c, p1_b_d)));
        let p2_eq_c_d = p2.clone()((p2_eq_a_b, (p2_a_c, p2_b_d)));
        f_eq_c_d.clone()((p1_eq_c_d, p2_eq_c_d))
    })
}

/// Converts core axiom to `POrFst`.
pub fn to_por_fst<A: DProp, B: Prop, C: DProp, D: Prop>(
    p: PSemNaive<Or<A, B>, C, A, D>
) -> POrFst<A, B, C, D> {
    Rc::new(move |(f, g)| {
        let p = p.clone();
        Rc::new(move |not_b| {
            let f = f.clone();
            let g = g.clone();
            match (A::decide(), C::decide()) {
                (_, Left(c)) => {
                    let or_a_b = quality::to_eq(f.clone()).1(c);
                    let a = and::exc_right((not_b, or_a_b));
                    p((f, (a.map_any(), g)))
                }
                (Left(a), Right(not_c)) => {
                    let c = quality::to_eq(f).0(Left(a));
                    match not_c(c) {}
                }
                (Right(not_a), _) => {
                    let h = Rc::new(move |or_a_b| {
                        match and::exc_both(((not_a.clone(), not_b.clone()), or_a_b)) {}
                    });
                    p((f, (h, g)))
                }
            }
        })
    })
}

/// Converts core axiom to `POrSnd`.
pub fn to_por_snd<A: Prop, B: DProp, C: DProp, D: Prop>(
    p: PSemNaive<Or<A, B>, C, B, D>
) -> POrSnd<A, B, C, D> {
    Rc::new(move |(f, g)| {
        let p = p.clone();
        Rc::new(move |not_a| {
            let f = f.clone();
            let g = g.clone();
            match (B::decide(), C::decide()) {
                (_, Left(c)) => {
                    let or_a_b = quality::to_eq(f.clone()).1(c);
                    let b = and::exc_left((not_a, or_a_b));
                    p((f, (b.map_any(), g)))
                }
                (Left(b), Right(not_c)) => {
                    let c = quality::to_eq(f.clone()).0(Right(b));
                    match not_c(c) {}
                }
                (Right(not_b), _) => {
                    let h = Rc::new(move |or_a_b| {
                        match and::exc_both(((not_a.clone(), not_b.clone()), or_a_b)) {}
                    });
                    p((f, (h, g)))
                }
            }
        })
    })
}

/// Converts core axiom to `PAndFst`.
pub fn to_pand_fst<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSemNaive<And<A, B>, C, A, D>
) -> PAndFst<A, B, C, D> {
    let y = Rc::new(move |(x, _)| x);
    Rc::new(move |(f, g)| p.clone()((f, (y.clone(), g))))
}

/// Converts core axiom to `PAndSnd`.
pub fn to_pand_snd<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSemNaive<And<A, B>, C, B, D>
) -> PAndSnd<A, B, C, D> {
    let y = Rc::new(move |(_, x)| x);
    Rc::new(move |(f, g)| p.clone()((f, (y.clone(), g))))
}

/// Use both `PAndFst` and `PAndSnd`.
///
/// This results in a stronger statement than `PAnd` alone.
pub fn use_pand_both<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Q<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> And<Q<A, C>, Q<B, C>> {
    let eq_a_c = p_a((f.clone(), g.clone()));
    let eq_b_c = p_b((f, g));
    (eq_a_c, eq_b_c)
}

/// Use both `PAndFst` and `PAndSnd` to prove `a = b`.
pub fn pand_both_eq<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Q<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> Q<A, B> {
    let (eq_a_c, eq_b_c) = path_semantics::use_pand_both(f, g, p_a, p_b);
    quality::transitivity(eq_a_c, quality::symmetry(eq_b_c))
}

/// Proves that types are unique.
pub fn uniq_ty<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
    eq_a_b: Q<A, B>,
    f: Imply<A, And<C, D>>,
    b_e: Imply<B, E>,
    p_a: PSemNaive<A, B, C, E>,
    p_b: PSemNaive<A, B, D, E>,
) -> Q<C, D> {
    let f_copy = f.clone();
    let a_c = Rc::new(move |x| f_copy(x).0);
    let a_d = Rc::new(move |x| f.clone()(x).1);
    let eq_c_e = p_a((eq_a_b.clone(), (a_c, b_e.clone())));
    let eq_d_e = p_b((eq_a_b, (a_d, b_e)));
    quality::transitivity(eq_c_e, quality::symmetry(eq_d_e))
}

/// Checks that `X` is qual to `T`.
pub fn check_q<T, X>(_: Q<X, T>) {}

/// Creation theorem.
///
/// For more information, see [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/creation-theorem.pdf).
pub fn creation<X: DProp, Y: DProp, A: Prop, B: Prop>(
    nx: Not<X>,
    ty_y_b: Ty<Y, B>,
    eqq_xy: EqQ<X, Y>,
    pord: POrdProof<X, A>,
) -> Imply<A, B> {
    let nx2 = nx.clone();
    let ty_x_a: Ty<X, A> = (Rc::new(move |x| not::absurd(nx2.clone(), x)), pord);
    let xy_ab = ty_eqq_imply(ty_x_a, ty_y_b, eqq_xy);
    let xy: Imply<X, Y> = Rc::new(move |x| not::absurd(nx.clone(), x));
    xy_ab.0(xy)
}

/// Creation theorem using homotopy map.
pub fn creation_hom<X: Prop, Y: Prop, A: Prop, B: Prop>(
    nx: Not<X>,
    ty_y_b: Ty<Y, B>,
    hom_xy: Hom<X, Y>,
    pord: POrdProof<X, A>,
) -> Imply<A, B> {
    let nx2 = nx.clone();
    let ty_x_a: Ty<X, A> = (Rc::new(move |x| not::absurd(nx2.clone(), x)), pord);
    let xy_ab = ty_hom_imply(ty_x_a, ty_y_b, hom_xy);
    let xy: Imply<X, Y> = Rc::new(move |x| not::absurd(nx.clone(), x));
    xy_ab.0(xy)
}
