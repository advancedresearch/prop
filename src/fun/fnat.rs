//! Natural numbers.

use super::*;

/// The type of natural numbers.
#[derive(Copy, Clone)]
pub struct Nat(());

/// `nat : type(0)`.
pub fn nat_ty() -> Ty<Nat, Type<Z>> {unimplemented!()}

/// Zero.
#[derive(Copy, Clone)]
pub struct Zero(());

/// `zero : nat`.
pub fn zero_ty() -> Ty<Zero, Type<Z>> {unimplemented!()}

/// Successor.
#[derive(Copy, Clone)]
pub struct Succ(());

/// `succ : nat -> nat`.
pub fn succ_ty() -> Ty<Succ, Pow<Nat, Nat>> {unimplemented!()}

/// Increment.
pub type Inc<N> = App<Succ, N>;
