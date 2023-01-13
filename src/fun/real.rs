//! Real numbers.

use super::*;

/// Real type.
#[derive(Copy, Clone)]
pub struct Real(());

/// Zero value.
#[derive(Copy, Clone)]
pub struct Zero(());

/// `real : type(0)`.
pub fn real_ty() -> Ty<Real, Type<Z>> {unimplemented!()}
/// `is_const(real)`.
pub fn real_is_const() -> IsConst<Real> {unimplemented!()}
/// `0 : real`.
pub fn zero_ty() -> Ty<Zero, Real> {unimplemented!()}
/// `is_const(zero)`.
pub fn zero_is_const() -> IsConst<Zero> {unimplemented!()}

/// `\(y : real) = y < aleph(0)`.
pub type Aleph0RealLam<Y> = Lam<Ty<Y, Real>, App<Lt, Tup<Y, Aleph<Z>>>>;
/// `(y : real, (\(y : real) = y < aleph(0))(y))`.
pub type Aleph0RealTy<Y> = DepTupTy<Y, Real, Aleph0RealLam<Y>>;
/// `(y, p) : (y : real, (\(y : real) = y < aleph(0))(y))`.
pub type Aleph0Real<Y, P> = DepTup<Y, Real, P, Aleph0RealLam<Y>>;
/// `\(a : real) = (x == (a + y))`.
pub type AddRealLam<X, A, Y> = Lam<Ty<A, Real>, Eq<X, App<Add, Tup<A, Y>>>>;
/// `(a : real, (\(a : real) = (x == (a + y)))(a))`.
pub type AddRealTy<X, A, Y> = DepTupTy<A, Real, AddRealLam<X, A, Y>>;
/// `(a, q) : (a : real, (\(a : real) = (x == (a + y)))(a))`.
pub type AddReal<X, A, Q, Y> = DepTup<A, Q, Real, AddRealLam<X, A, Y>>;

/// `((a, q) : (a : real, (\(a : real) = (x == (a + y)))(a)))^
///  ((y, p) : (y : real, (\(y : real) = y < aleph(0))(y)))`
pub type RealDef<X, A, Q, Y, P> = Pow<AddReal<X, A, Q, Y>, Aleph0Real<Y, P>>;

/// Definition of real.
pub fn real_def<X: Prop, A: Prop, Q: Prop, Y: Prop, P: Prop>(
    _ty_x: Ty<X, Real>
) -> RealDef<X, A, Q, Y, P> {unimplemented!()}

/// Addition.
#[derive(Copy, Clone)]
pub struct Add(());

/// Negation.
#[derive(Copy, Clone)]
pub struct Neg(());

/// Subtraction.
#[derive(Copy, Clone)]
pub struct Sub(());

/// Less than.
#[derive(Copy, Clone)]
pub struct Lt(());

/// Infinite cardinality.
#[derive(Copy, Clone)]
pub struct Aleph<N>(N);
