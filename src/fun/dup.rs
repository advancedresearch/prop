use super::*;

/// Duplicate function.
#[derive(Clone, Copy)]
pub struct Dup(());

/// `dup : a -> (a, a)`.
///
/// Type of Dup.
pub fn dup_ty<A: Prop>() -> Ty<Dup, Pow<Tup<A, A>, A>> {unimplemented!()}
/// `is_const(dup)`.
pub fn dup_is_const() -> IsConst<Dup> {unimplemented!()}

/// `dup(a) = (a, a)`.
///
/// Definition of Dup function.
pub fn dup_def<A: Prop>() -> Eq<App<Dup, A>, Tup<A, A>> {unimplemented!()}
