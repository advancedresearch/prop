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

use nat::*;

/// Core axiom of Path Semantics.
pub type PSem<F1, F2, X1, X2> = Imply<
    And<And<Eq<F1, F2>, And<POrdProof<F1, X1>, POrdProof<F2, X2>>>,
        And<Imply<F1, X1>, Imply<F2, X2>>>,
    Eq<X1, X2>,
>;

/// Naive axiom of Path Semantics (without order assumption).
pub type PSemNaive<F1, F2, X1, X2> = Imply<
    And<Eq<F1, F2>, And<Imply<F1, X1>, Imply<F2, X2>>>,
    Eq<X1, X2>
>;

/// Lifts `A` to higher level.
pub type PLift<A, B, C> = Imply<
    And<Eq<A, B>, Imply<B, C>>,
    Eq<A, C>
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
pub type PAnd<A, B, C, D> = PLift<And<A, B>, C, D>;

/// Sends first argument of Logical OR to higher level.
pub type POrFst<A, B, C, D> = Imply<
    And<Eq<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<B>, Eq<A, D>>
>;

/// Sends second argument of Logical OR to higher level.
pub type POrSnd<A, B, C, D> = Imply<
    And<Eq<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<A>, Eq<B, D>>
>;

/// Sends Logical OR to higher level.
pub type POr<A, B, C, D> = PLift<Or<A, B>, C, D>;

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

impl<A, B, T> POrd<T> for And<A, B>
    where A: POrd<T>, B: POrd<T> {}
impl<A, B, T> POrd<T> for Or<A, B>
    where A: POrd<T>, B: POrd<T> {}
impl<A, B, T> POrd<T> for Imply<A, B>
    where A: POrd<T>, B: POrd<T> {}

/// Path semantical proposition level.
pub trait LProp: Prop {
    /// The level.
    type N: Clone;
    /// Sets proposition level.
    type SetLevel<T: 'static + Clone>: LProp;
}
/// True for a path semantical level.
#[derive(Copy, Clone)]
pub struct LTrue<N>(pub N);
impl<U: 'static + Clone> LProp for LTrue<U> {
    type N = U;
    type SetLevel<T: 'static + Clone> = LTrue<T>;
}
impl LProp for False {
    type N = NaN;
    type SetLevel<T: 'static + Clone> = Self;
}
/// Increases proposition level of `A` with some amount `N`.
pub type IncLevel<A, N> = <A as LProp>::SetLevel<<(<A as LProp>::N, N) as Add>::Out>;
/// Increases level one step.
pub type Inc<A> = <A as LProp>::SetLevel<S<<A as LProp>::N>>;

impl<N: 'static + Default + Clone> Decidable for LTrue<N> {
    fn decide() -> ExcM<Self> {Either::Left(LTrue(N::default()))}
}

impl<N: Default> Default for LTrue<N> {
    fn default() -> Self {LTrue(N::default())}
}

impl<T, U> POrd<U> for T where T: LProp, U: LProp, T::N: Lt<U::N> {}

/// Shorthand for decidable proposition with path semantical level.
pub trait DLProp: LProp + DProp {}
impl<T: LProp + DProp> DLProp for T {}

/// Returns the minimum LProp.
pub type Min<A, B> = <(<A as LProp>::N, <B as LProp>::N) as SortMin<A, B>>::Out;
/// Returns the maximum LProp.
pub type Max<A, B> = <(<A as LProp>::N, <B as LProp>::N) as SortMax<A, B>>::Out;
/// Normalise 4 `LProp`s (sorted ascending by propositional level).
pub type Normalise<A, B, C, D> = (
    Min<Min<A, B>, Min<C, D>>,
    Min<Max<Min<A, B>, Min<C, D>>, Min<Max<A, B>, Max<C, D>>>,
    Max<Max<Min<A, B>, Min<C, D>>, Min<Max<A, B>, Max<C, D>>>,
    Max<Max<A, B>, Max<C, D>>,
);

/// Look by index.
pub trait Lookup<N> {
    /// The output type.
    type Out;
}
impl<A, B, C, D> Lookup<Zero> for (A, B, C, D) {type Out = A;}
impl<A, B, C, D> Lookup<One> for (A, B, C, D) {type Out = B;}
impl<A, B, C, D> Lookup<Two> for (A, B, C, D) {type Out = C;}
impl<A, B, C, D> Lookup<Three> for (A, B, C, D) {type Out = D;}

/// Look up type `N` among the normalised `A, B, C, D`.
pub type LN<N, A, B, C, D> = <Normalise<A, B, C, D> as Lookup<N>>::Out;

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

/// Sorts two types.
pub trait SortMin<T: LProp, U: LProp> {
    /// The output type.
    type Out: LProp;
}

impl<T: LProp, U: LProp> SortMin<T, U> for (Z, Z) {
    type Out = T;
}
impl<T: LProp, U: LProp, N> SortMin<T, U> for (Z, S<N>) {
    type Out = T;
}
impl<T: LProp, U: LProp, N> SortMin<T, U> for (S<N>, Z) {
    type Out = U;
}
impl<T: LProp, U: LProp, N, M> SortMin<T, U> for (S<N>, S<M>)
    where (N, M): SortMin<T, U>
{
    type Out = <(N, M) as SortMin<T, U>>::Out;
}

/// Sorts two types.
pub trait SortMax<T: LProp, U: LProp> {
    /// The output type.
    type Out: LProp;
}

impl<T: LProp, U: LProp> SortMax<T, U> for (Z, Z) {
    type Out = U;
}
impl<T: LProp, U: LProp, N> SortMax<T, U> for (Z, S<N>) {
    type Out = U;
}
impl<T: LProp, U: LProp, N> SortMax<T, U> for (S<N>, Z) {
    type Out = T;
}
impl<T: LProp, U: LProp, N, M> SortMax<T, U> for (S<N>, S<M>)
    where (N, M): SortMax<T, U>
{
    type Out = <(N, M) as SortMax<T, U>>::Out;
}

#[cfg(test)]
pub mod tests {
    use super::*;

    fn check_sort_min<X, Y, U: LProp, T: LProp>() where (X, Y): SortMin<U, T> {}

    pub fn sort_min<T: LProp, U: LProp>() {
        check_sort_min::<Z, Z, T, U>();
        check_sort_min::<S<Z>, Z, T, U>();
        check_sort_min::<Z, S<Z>, T, U>();
        check_sort_min::<S<Z>, S<Z>, T, U>();
    }
}

/// The decided minimum (1st of 4).
pub type MinMin<A, B, C, D> = Min<Min<A, B>, Min<C, D>>;
/// The undecided maximum minimum.
pub type MaxMin<A, B, C, D> = Max<Min<A, B>, Min<C, D>>;
/// The undecided minimum maximum.
pub type MinMax<A, B, C, D> = Min<Max<A, B>, Max<C, D>>;
/// The decided maximum (4th of 4).
pub type MaxMax<A, B, C, D> = Max<Max<A, B>, Max<C, D>>;
/// The decided minimum of undecided middle (2nd of 4).
pub type Mixi<A, B, C, D> = Min<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>;
/// The decided maximum of undecided middle (3rd of 4).
pub type Maxi<A, B, C, D> = Max<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>;

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

/// Get reflection equality from equality between different propositions.
///
/// This is used as alternative to `eq::refl` for path witness in Path Semantics.
/// See https://github.com/advancedresearch/prop/issues/124 for more information.
pub fn refl_left<A: Prop, B: Prop>(eq: Eq<A, B>) -> Eq<A, A> {
    eq::in_right_arg(eq.clone(), eq::commute(eq))
}

/// Get reflection equality from equality between different propositions.
///
/// This is used as alternative to `eq::refl` for path witness in Path Semantics.
/// See https://github.com/advancedresearch/prop/issues/124 for more information.
pub fn refl_right<A: Prop, B: Prop>(eq: Eq<A, B>) -> Eq<B, B> {
    eq::in_left_arg(eq.clone(), eq)
}

/// Reduce naive core axiom in case of false to equality of associated propositions.
pub fn naive_red_false<A: Prop, B: Prop>(
    p: PSemNaive<False, False, A, B>
) -> Eq<A, B> {
    p((eq::refl(), (imply::absurd(), imply::absurd())))
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

/// `(a b) (c d): ¬a ∧ ¬b ∧ (a => c) ∧ (b => d) => (c = d)`.
pub fn neg<A: Prop, B: Prop, C: Prop, D: Prop>(
    not_a: Not<A>,
    not_b: Not<B>,
    pr_a_c: POrdProof<A, C>,
    pr_b_d: POrdProof<B, D>,
    a_c: Imply<A, C>,
    b_d: Imply<B, D>,
    p: PSem<A, B, C, D>,
) -> Eq<C, D> {
    p(((and::to_eq_neg((not_a, not_b)), (pr_a_c, pr_b_d)), (a_c, b_d)))
}

/// `(a b) (c d): ¬a ∧ ¬b ∧ a => c ∧ b => d => c = d`.
pub fn naive_neg<A: Prop, B: Prop, C: Prop, D: Prop>(
    not_a: Not<A>,
    not_b: Not<B>,
    a_c: Imply<A, C>,
    b_d: Imply<B, D>,
    p: PSemNaive<A, B, C, D>,
) -> Eq<C, D> {
    p((and::to_eq_neg((not_a, not_b)), (a_c, b_d)))
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
    f_eq_a_b: Imply<Eq<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>>,
                And<Eq<A, B>, Eq<LN<Zero, A, B, C, D>, LN<One, A, B, C, D>>>>,
    f_a_c: Imply<Imply<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>>,
                 And<Imply<A, C>, Imply<LN<Zero, A, B, C, D>, LN<Two, A, B, C, D>>>>,
    f_b_d: Imply<Imply<B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>,
                       D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>>,
                 And<Imply<B, D>, Imply<LN<One, A, B, C, D>, LN<Three, A, B, C, D>>>>,
    f_eq_c_d: Imply<And<Eq<C, D>, Eq<LN<Two, A, B, C, D>, LN<Three, A, B, C, D>>>,
                    Eq<C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>,
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
                    let or_a_b = f.1(c);
                    let a = and::exc_right((not_b, or_a_b));
                    p((f, (a.map_any(), g)))
                }
                (Left(a), Right(not_c)) => {
                    let c = f.0(Left(a));
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
                    let or_a_b = f.1(c);
                    let b = and::exc_left((not_a, or_a_b));
                    p((f, (b.map_any(), g)))
                }
                (Left(b), Right(not_c)) => {
                    let c = f.0(Right(b));
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

/// Join either `POrFst` and `POrSnd`.
pub fn por_join_either<A: DProp, B: DProp, C: Prop, D: Prop>(
    p: Or<POrFst<A, B, C, D>, POrSnd<A, B, C, D>>,
) -> POr<A, B, C, D> {
    match p {
        Left(p1) => {
            Rc::new(move |(eq_f_c, g)| {
                let not_b_eq_a_d = p1.clone()((eq_f_c.clone(), g.clone()));
                let imply_or_a_b_d: Imply<Or<A, B>, D> = imply::in_left_arg(g, eq::commute(eq_f_c));

                let eq_or_a_b_d: Eq<Or<A, B>, D> = (
                    Rc::new(move |or_a_b: Or<A, B>| {
                        let imply_or_a_b_d = imply_or_a_b_d.clone();
                        match or_a_b {
                            Left(a) => imply_or_a_b_d(Left(a)),
                            Right(b) => imply_or_a_b_d(Right(b)),
                        }
                    }),
                    Rc::new(move |d: D| {
                        match B::decide() {
                            Left(b) => Right(b),
                            Right(not_b) => Left(not_b_eq_a_d.clone()(not_b).1(d)),
                        }
                    })
                );
                eq_or_a_b_d
            })
        }
        Right(p2) => {
            Rc::new(move |(eq_f_c, g)| {
                let not_a_eq_b_d = p2.clone()((eq_f_c.clone(), g.clone()));
                let imply_or_a_b_d: Imply<Or<A, B>, D> = imply::in_left_arg(g, eq::commute(eq_f_c));

                let eq_or_a_b_d: Eq<Or<A, B>, D> = (
                    Rc::new(move |or_a_b: Or<A, B>| {
                        let imply_or_a_b_d = imply_or_a_b_d.clone();
                        match or_a_b {
                            Left(a) => imply_or_a_b_d(Left(a)),
                            Right(b) => imply_or_a_b_d(Right(b)),
                        }
                    }),
                    Rc::new(move |d: D| {
                        match A::decide() {
                            Left(a) => Left(a),
                            Right(not_a) => Right(not_a_eq_b_d.clone()(not_a).1(d)),
                        }
                    })
                );
                eq_or_a_b_d
            })
        }
    }
}

/// Transports core axiom using equivalence in the `C` corner.
pub fn by_eq_c<A: Prop, B: Prop, C: Prop, D: Prop, C2: Prop>(
    p: PSem<A, B, C, D>,
    eq_c_c2: Eq<C, C2>,
) -> PSem<A, B, C2, D> {
    Rc::new(move |((f, (pr_a_c, pr_b_d)), (g, h))| {
        let eq_c_c2 = eq_c_c2.clone();
        let eq_c_c2_clone = eq_c_c2.clone();
        let eq_c_c2_clone2 = eq_c_c2.clone();
        let pr2 = pr_a_c.by_eq_right(eq::commute(eq_c_c2.clone()));
        let g2 = Rc::new(move |a| eq_c_c2_clone2.1(g.clone()(a)));
        let eq_c_d = p(((f, (pr2, pr_b_d)), (g2, h)));
        let eq_c_d_clone = eq_c_d.clone();
        (Rc::new(move |c2| eq_c_d_clone.0(eq_c_c2_clone.1(c2))),
         Rc::new(move |d| eq_c_c2.0(eq_c_d.clone().1(d))))
    })
}

/// Transports naive core axiom using equivalence in the `C` corner.
pub fn naive_by_eq_c<A: Prop, B: Prop, C: Prop, D: Prop, C2: Prop>(
    p: PSemNaive<A, B, C, D>,
    eq_c_c2: Eq<C, C2>,
) -> PSemNaive<A, B, C2, D> {
    Rc::new(move |(f, (g, h))| {
        let eq_c_c2 = eq_c_c2.clone();
        let eq_c_c2_clone = eq_c_c2.clone();
        let eq_c_c2_clone2 = eq_c_c2.clone();
        let g2 = Rc::new(move |a| eq_c_c2_clone2.1(g.clone()(a)));
        let eq_c_d = p((f, (g2, h)));
        let eq_c_d_clone = eq_c_d.clone();
        (Rc::new(move |c2| eq_c_d_clone.0(eq_c_c2_clone.1(c2))),
         Rc::new(move |d| eq_c_c2.0(eq_c_d.clone().1(d))))
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
    p_a: PSemNaive<A, B, C, E>,
    p_b: PSemNaive<A, B, D, E>,
) -> Eq<C, D> {
    let f_copy = f.clone();
    let a_c = Rc::new(move |x| f_copy(x).0);
    let a_d = Rc::new(move |x| f.clone()(x).1);
    let eq_c_e = p_a((eq_a_b.clone(), (a_c, b_e.clone())));
    let eq_d_e = p_b((eq_a_b, (a_d, b_e)));
    eq::transitivity(eq_c_e, eq::commute(eq_d_e))
}

/// Checks whether two proposition levels are equal.
pub fn eq_lev<A: LProp, B: LProp>(_a: A, _b: B) where (A::N, B::N): EqNat {}
/// Checks whether a proposition level is less than another.
pub fn lt_lev<A: LProp, B: LProp>(_a: A, _b: B) where A::N: Lt<B::N> {}

/// Checks that `X` is equal to `T`.
pub fn check_eq<T, X>(_: Eq<X, T>) {}

#[cfg(test)]
#[allow(dead_code)]
mod test {
    use super::*;

    fn check_nan<A: LProp<N = NaN>, B: LProp<N = NaN>>(a: A, b: B) {eq_lev(a, b)}
    fn check_zero<A: LProp<N = Zero>, B: LProp<N = Zero>>(a: A, b: B) {eq_lev(a, b)}
    fn check_one<A: LProp<N = One>, B: LProp<N = One>>(a: A, b: B) {eq_lev(a, b)}
    fn check_zero_one<A: LProp<N = Zero>, B: LProp<N = One>>(a: A, b: B) {lt_lev(a, b)}
    fn check_undef_nan<A: LProp, B: LProp<N = NaN>>(a: A, b: B)
        where A::N: Lt<NaN>, NaN: Lt<A::N>
    {
        eq_lev(a, b)
    }
    fn check_one_two() {lt_lev(LTrue(_1), LTrue(_2))}
}
