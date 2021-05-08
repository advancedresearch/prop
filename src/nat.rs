//! Natural numbers with types.

use crate::Prop;

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
pub struct NaN;

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

/// Zero.
pub const _0: Zero = Z;
/// One.
pub const _1: One = S(Z);
/// Two.
pub const _2: Two = S(_1);

/// Less than comparison.
#[marker]
pub trait Lt<T> {}
impl Lt<S<Z>> for Z {}
impl<T> Lt<S<S<T>>> for S<T> {}
impl<T: Lt<U>, U> Lt<S<U>> for T {}

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
pub trait Nat: Prop + Lt<S<Self>> + Default {}
impl<T> Nat for T where T: Prop + Lt<S<T>> + Default {}

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
