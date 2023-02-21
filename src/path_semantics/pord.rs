use super::*;

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
    pub fn by_eq_left<V>(self, _: Eq<T, V>) -> POrdProof<V, U> {
        POrdProof(std::marker::PhantomData)
    }

    /// Transform right argument by equivalence.
    pub fn by_eq_right<V>(self, eq: Eq<U, V>) -> POrdProof<T, V> {
        self.by_imply_right(eq.0)
    }

    /// Transform right argument by implication.
    pub fn by_imply_right<V>(self, _: Imply<U, V>) -> POrdProof<T, V> {
        POrdProof(std::marker::PhantomData)
    }

    /// Merges two proofs of order at right side.
    pub fn merge_right<V>(self, _: POrdProof<T, V>) -> POrdProof<T, And<U, V>> {
        POrdProof(std::marker::PhantomData)
    }

    /// Merges two proofs of order at left side.
    pub fn merge_left<V>(self, _: POrdProof<V, U>) -> POrdProof<And<T, V>, U> {
        POrdProof(std::marker::PhantomData)
    }

    /// Combine two proofs into one using AND.
    pub fn and<T2, U2>(self, _: POrdProof<T2, U2>) -> POrdProof<And<T, T2>, And<U, U2>> {
        POrdProof(std::marker::PhantomData)
    }

    /// Combine two proofs into one using OR.
    pub fn or<T2, U2>(self, _: POrdProof<T2, U2>) -> POrdProof<Or<T, T2>, Or<U, U2>> {
        POrdProof(std::marker::PhantomData)
    }

    /// Combine two proofs into one using IMPLY.
    pub fn imply<T2, U2>(self, _: POrdProof<T2, U2>) -> POrdProof<Imply<T, T2>, Imply<U, U2>> {
        POrdProof(std::marker::PhantomData)
    }

    /// Combine two proofs into one using EQ.
    pub fn eq<T2, U2>(self, x: POrdProof<T2, U2>) -> POrdProof<Eq<T, T2>, Eq<U, U2>> {
        self.clone().imply(x.clone()).and(x.imply(self))
    }

    /// Lift to qubit.
    pub fn qu(self) -> POrdProof<Qu<T>, Qu<U>> {
        POrdProof(std::marker::PhantomData)
    }

    /// Combine two proofs into one using path semantical quality.
    pub fn q<T2, U2>(self, x: POrdProof<T2, U2>) -> POrdProof<Q<T, T2>, Q<U, U2>> {
        self.clone().eq(x.clone()).and(self.qu().and(x.qu()))
    }
}

impl<A, B, C> POrdProof<A, Or<B, C>> {
    /// Get sub order proof `a < b`.
    pub fn or_left(self) -> POrdProof<A, B> {
        POrdProof(std::marker::PhantomData)
    }

    /// Get sub order proof `a < c`.
    pub fn or_right(self) -> POrdProof<A, C> {
        POrdProof(std::marker::PhantomData)
    }
}

impl<A, B> POrdProof<A, Imply<A, B>> {
    /// Get reduced proof `a < b`.
    pub fn imply_reduce(self) -> POrdProof<A, B> {
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
impl<A, B> POrd<Qu<B>> for Qu<A>
    where A: POrd<B> {}

impl<T, U> POrd<U> for T where T: LProp, U: LProp, T::N: Lt<U::N> {}
