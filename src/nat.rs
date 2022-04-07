//! Natural numbers with types.

use crate::{Eq, Prop, Not};

/// Zero.
#[derive(Copy, Clone)]
pub struct Z;
/// Successor.
#[derive(Copy, Clone)]
pub struct S<T>(pub T);
/// Not-a-number.
///
/// This is less than all other numbers, including itself.
///
/// Is used by `False` as path semantical propositional level.
#[derive(Copy, Clone)]
pub enum NaN {}

impl Default for Z {
    fn default() -> Z {Z}
}
impl<T: Default> Default for S<T> {
    fn default() -> Self {S(T::default())}
}

/// The zero type.
pub type Zero = Z;
/// The one type.
pub type One = S<Zero>;
/// The two type.
pub type Two = S<One>;
/// The three type.
pub type Three = S<Two>;

/// 0.
pub const _0: Zero = Z;
/// 1.
pub const _1: One = S(Z);
/// 2.
pub const _2: Two = S(_1);
/// 3.
pub const _3: Three = S(_2);

/// Less than comparison.
#[marker]
pub trait Lt<T> {}
impl<T> Lt<S<T>> for Z {}
impl<T> Lt<S<S<T>>> for S<T> {}
impl<T: Lt<U>, U> Lt<S<U>> for T {}

/// Provides a proof that the numbers are inequal.
pub fn lt_neq<T: Lt<U>, U>() -> Not<Eq<T, U>> {
    unimplemented!()
}

/// Whether two natural numbers are equal.
#[marker]
pub trait EqNat {}
impl<T> EqNat for (T, T) {}
impl<T, U> EqNat for (T, U) where T: Lt<U>, U: Lt<T> {}

/// Check that one natural number is less than the other.
pub fn lt<T: Lt<U>, U>(_a: T, _b: U) {}
/// Check that one natural number is equal to the other.
pub fn eq<T, U>(_a: T, _b: U) where (T, U): EqNat {}

/// Implemented for natural numbers.
pub trait Nat: Prop + Lt<S<Self>> + Dec + Default {}
impl<T> Nat for T where T: Prop + Lt<S<T>> + Dec + Default {}

/// Addition.
pub trait Add {
    /// The output type.
    type Out: Clone;
}
impl Add for (Z, Z) {
    type Out = Z;
}
impl<T: Clone> Add for (Z, S<T>) {
    type Out = S<T>;
}
impl<T, U> Add for (S<T>, U) where (T, U): Add {
    type Out = S<<(T, U) as Add>::Out>;
}

/// Decrement.
pub trait Dec {
    /// The output type.
    type Out: Nat;
}
impl Dec for Z {
    type Out = Z;
}
impl<T: Nat> Dec for S<T> {
    type Out = T;
}
