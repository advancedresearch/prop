//! # Path Semantics
//!
//! Path Semantics has a core axiom which is used to model mathematics.
//!
//! This core axiom is modelled here,
//! lifting proof of path semantical order to expressions of propositions.
//!
//! For more information, see
//! https://github.com/advancedresearch/path_semantics.

use crate::*;

/// Core axiom of Path Semantics.
pub type PSem<F1, F2, X1, X2> = Imply<
    And<And<Eq<F1, F2>, POrdProof<F1, X1>>,
        And<Imply<F1, X1>, Imply<F2, X2>>>,
    Eq<X1, X2>,
>;

/// Naive axiom of Path Semantics (without order assumption).
pub type PSemNaive<F1, F2, X1, X2> = Imply<
    And<Eq<F1, F2>, And<Imply<F1, X1>, Imply<F2, X2>>>,
    Eq<X1, X2>
>;

/// Sends first argument of Logical AND to higher level.
pub type PAndFst<A, B, C, D> = Imply<
    And<Eq<And<A, B>, C>, Imply<C, D>>,
    Eq<A, D>,
>;
/// Sends second argument of Logical AND to higher level.
pub type PAndSnd<A, B, C, D> = Imply<
    And<Eq<And<A, B>, C>, Imply<C, D>>,
    Eq<B, D>,
>;
/// Sends Logical AND to higher level.
pub type PAnd<A, B, C, D> = Imply<
    And<Eq<And<A, B>, C>, Imply<C, D>>,
    Eq<And<A, B>, D>
>;

/// Proof of path semantical order.
#[derive(Copy)]
pub struct POrdProof<T, U>(std::marker::PhantomData<(T, U)>);

impl<T: POrd<U>, U> Default for POrdProof<T, U> {
    fn default() -> Self {
        POrdProof(std::marker::PhantomData)
    }
}

impl<T, U> Clone for POrdProof<T, U> {
    fn clone(&self) -> POrdProof<T, U> {
        POrdProof(std::marker::PhantomData)
    }
}

impl<T: 'static, U: 'static> Decidable for POrdProof<T, U> {
    fn decide() -> ExcM<POrdProof<T, U>> {
        Left(POrdProof(std::marker::PhantomData))
    }
}

impl<T, U> POrdProof<T, U> {
    /// Creates a new proof from trait constraints.
    pub fn new() -> Self where T: POrd<U> {
        Self::default()
    }

    /// Transivity of path semantical order.
    pub fn transitivity<V>(self, _: POrdProof<U, V>) -> POrdProof<T, V> {
        POrdProof(std::marker::PhantomData)
    }

    /// Transform left argument by equivalence.
    pub fn by_eq_left<V>(self, eq: Eq<T, V>) -> POrdProof<V, U> {
        self.by_imply_left(eq.1)
    }

    /// Transform right argument by equivalence.
    pub fn by_eq_right<V>(self, eq: Eq<U, V>) -> POrdProof<T, V> {
        self.by_imply_right(eq.0)
    }

    /// Transform left argument by implication.
    pub fn by_imply_left<V>(self, _: Imply<V, T>) -> POrdProof<V, U> {
        POrdProof(std::marker::PhantomData)
    }

    /// Transform right argument by implication.
    pub fn by_imply_right<V>(self, _: Imply<U, V>) -> POrdProof<T, V> {
        POrdProof(std::marker::PhantomData)
    }
}

/// Path semantical order.
///
/// This is implemented by types to define an order
/// such that symbols can not be used inconsistently.
///
/// Uses a marker feature to allow overlapping impls.
#[marker]
pub trait POrd<T> {}

/// Path semantical order for binary operators.
pub trait PBinOrd {
    /// The left argument.
    type Left;
    /// The right argument.
    type Right;
}

impl<T> POrd<T::Left> for T where T: PBinOrd {}
impl<T> POrd<T::Right> for T where T: PBinOrd {}
impl<T> POrd<T> for False {}
impl<T, U> PBinOrd for And<T, U> {
    type Left = T;
    type Right = U;
}
impl<T, U> PBinOrd for Or<T, U> {
    type Left = T;
    type Right = U;
}
impl<T, U> PBinOrd for Imply<T, U> {
    type Left = T;
    type Right = U;
}
impl<T, U> PBinOrd for POrdProof<T, U> {
    type Left = T;
    type Right = U;
}

/// Path semantical proposition level.
pub trait LProp: Prop {
    /// The level.
    type N;
}
/// Shorthand for decidable proposition.
pub trait DLProp: LProp + DProp {}
impl<T: LProp + DProp> DLProp for T {}

/// Reduce core axiom in case of false to equality of associated propositions.
pub fn red_false<A: Prop, B: Prop>(
    p: PSem<False, False, A, B>
) -> Eq<A, B> {
    p(((eq::refl(), POrdProof::new()), (imply::absurd(), imply::absurd())))
}

/// Composition.
pub fn comp<F1: Prop, F2: Prop, F3: Prop, F4: Prop, X1: Prop, X2: Prop>(
    f: PSem<F1, F2, F3, F4>,
    g: PSem<F3, F4, X1, X2>,
    pr_f1_f3: POrdProof<F1, F3>,
    pr_f3_x1: POrdProof<F3, X1>,
    f1_f3: Imply<F1, F3>,
    f2_f4: Imply<F2, F4>,
    f3_x1: Imply<F3, X1>,
    f4_x2: Imply<F4, X2>,
) -> PSem<F1, F2, X1, X2> {
    Rc::new(move |((f1_eq_f2, _pr_f1_x1), (_f1_x1, _f2_x2))| {
        let f3_eq_f4 = f(((f1_eq_f2, pr_f1_f3.clone()), (f1_f3.clone(), f2_f4.clone())));
        let x1_eq_x2 = g(((f3_eq_f4, pr_f3_x1.clone()), (f3_x1.clone(), f4_x2.clone())));
        x1_eq_x2
    })
}

/// Converts core axiom to `PAndFst`.
pub fn to_pand_fst<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSem<And<A, B>, C, A, D>
) -> PAndFst<A, B, C, D> {
    let x: POrdProof<And<A, B>, A> = POrdProof::new();
    let y = Rc::new(move |(x, _)| x);
    Rc::new(move |(f, g)| p.clone()(((f, x.clone()), (y.clone(), g))))
}

/// Converts core axiom to `PAndSnd`.
pub fn to_pand_snd<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSem<And<A, B>, C, B, D>
) -> PAndSnd<A, B, C, D> {
    let x: POrdProof<And<A, B>, B> = POrdProof::new();
    let y = Rc::new(move |(_, x)| x);
    Rc::new(move |(f, g)| p.clone()(((f, x.clone()), (y.clone(), g))))
}

/// Join `PAndFst` and `PAndSnd`.
pub fn pand_join<A: Prop, B: Prop, C: Prop, D: Prop>(
    p1: PAndFst<A, B, C, D>,
    p2: PAndSnd<A, B, C, D>,
) -> PAnd<A, B, C, D> {
    Rc::new(move |(eq_f_c, g)| {
        let eq_a_d = p1.clone()((eq_f_c.clone(), g.clone()));
        let eq_b_d = p2.clone()((eq_f_c, g));
        let eq_a_d_copy = eq_a_d.clone();
        let eq_ab_d: Eq<And<A, B>, D> = (Rc::new(move |(a, _)| eq_a_d_copy.0(a)),
                       Rc::new(move |d| (eq_a_d.clone().1(d.clone()), eq_b_d.clone().1(d))));
        eq_ab_d
    })
}

/// Use both `PAndFst` and `PAndSnd`.
///
/// This results in a stronger statement than `PAnd` alone.
pub fn use_pand_both<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Eq<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> And<Eq<A, C>, Eq<B, C>> {
    let eq_a_c = p_a((f.clone(), g.clone()));
    let eq_b_c = p_b((f, g));
    (eq_a_c, eq_b_c)
}

/// Use both `PAndFst` and `PAndSnd` to prove `a = b`.
pub fn pand_both_eq<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Eq<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> Eq<A, B> {
    let (eq_a_c, eq_b_c) = path_semantics::use_pand_both(f, g, p_a, p_b);
    eq::transitivity(eq_a_c, eq::commute(eq_b_c))
}

/// Proves that types are unique.
pub fn uniq_ty<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
    eq_a_b: Eq<A, B>,
    f: Imply<A, And<C, D>>,
    b_e: Imply<B, E>,
    p_a: PSem<A, B, C, E>,
    p_b: PSem<A, B, D, E>,
) -> Eq<C, D> {
    let pr_cd_c: POrdProof<And<C, D>, C> = POrdProof::new();
    let pr_cd_d: POrdProof<And<C, D>, D> = POrdProof::new();
    let f_copy = f.clone();
    let pr_a_c = pr_cd_c.by_imply_left(f_copy);
    let f_copy = f.clone();
    let pr_a_d = pr_cd_d.by_imply_left(f_copy);
    let f_copy = f.clone();
    let a_c = Rc::new(move |x| f_copy(x).0);
    let a_d = Rc::new(move |x| f.clone()(x).1);
    let eq_c_e = p_a(((eq_a_b.clone(), pr_a_c), (a_c, b_e.clone())));
    let eq_d_e = p_b(((eq_a_b, pr_a_d), (a_d, b_e)));
    eq::transitivity(eq_c_e, eq::commute(eq_d_e))
}
