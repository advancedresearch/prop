//! Finite sets.

use super::*;
use fnat::{Nat, Succ, Zero};

/// A finite set.
#[derive(Copy, Clone)]
pub struct Fin(());

/// `fin : nat -> type(0)`.
pub fn fin_ty() -> Ty<Fin, Pow<Type<Zero>, Nat>> {unimplemented!()}

/// An empty set.
#[derive(Copy, Clone)]
pub struct Empty(());

/// `(n : nat)  =>  (empty : fin(n + 1))`.
pub fn empty_ty<N>(_n_ty: Ty<N, Nat>) -> Ty<Empty, App<Fin, App<Succ, N>>> {unimplemented!()}

/// A finite set.
#[derive(Copy, Clone)]
pub struct FinSucc(());

/// `(n : nat)  =>  fin_succ : fin(n) -> fin(n + 1)`.
pub fn fin_succ_ty<N>(_n_ty: Ty<N, Nat>) -> Ty<FinSucc, Pow<App<Fin, App<Succ, N>>, App<Fin, N>>>
{unimplemented!()}
