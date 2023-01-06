use super::*;

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
impl<U: LProp> LProp for Q<U, U> {
    type N = U::N;
    type SetLevel<T: 'static + Clone> = Q<U::SetLevel<T>, U::SetLevel<T>>;
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

/// Shorthand for decidable proposition with path semantical level.
pub trait DLProp: LProp + DProp {}
impl<T: LProp + DProp> DLProp for T {}

/// Shorthand for existential proposition with path semantical level.
pub trait ELProp: LProp + EProp {}
impl<T: LProp + EProp> ELProp for T {}

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

/// Checks whether two proposition levels are equal.
pub fn eq_lev<A: LProp, B: LProp>(_a: A, _b: B) where (A::N, B::N): EqNat {}
/// Checks whether a proposition level is less than another.
pub fn lt_lev<A: LProp, B: LProp>(_a: A, _b: B) where A::N: Lt<B::N> {}

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

    pub fn check_nan<A: LProp<N = NaN>, B: LProp<N = NaN>>(a: A, b: B) {eq_lev(a, b)}
    pub fn check_zero<A: LProp<N = Zero>, B: LProp<N = Zero>>(a: A, b: B) {eq_lev(a, b)}
    pub fn check_one<A: LProp<N = One>, B: LProp<N = One>>(a: A, b: B) {eq_lev(a, b)}
    pub fn check_zero_one<A: LProp<N = Zero>, B: LProp<N = One>>(a: A, b: B) {lt_lev(a, b)}
    pub fn check_undef_nan<A: LProp, B: LProp<N = NaN>>(a: A, b: B)
        where A::N: Lt<NaN>, NaN: Lt<A::N>
    {
        eq_lev(a, b)
    }
    pub fn check_one_two() {lt_lev(LTrue(_1), LTrue(_2))}
}
