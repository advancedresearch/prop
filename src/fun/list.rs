//! List.

use super::*;

/// A list.
pub struct List(());

/// `(a : type(0))  =>  (list : a -> type(0))`.
pub fn list_ty<A: Prop>(_a_ty: Ty<A, Type<Z>>) -> Ty<List, Pow<Type<Z>, A>> {unimplemented!()}

/// An empty list.
pub struct Nil(());

/// `(a : type(0))  =>  (nil : list(a))`.
pub fn nil_ty<A: Prop>(_a_ty: Ty<A, Type<Z>>) -> Ty<Nil, App<List, A>> {unimplemented!()}

/// List concatenation.
pub struct Concat(());

/// `(a : type(0))  =>  (concat : (list(a), list(a)) -> list(a))`.
pub fn concat_ty<A: Prop>(
    _a_ty: Ty<A, Type<Z>>
) -> Ty<Concat, Pow<App<List, A>, Tup<App<List, A>, App<List, A>>>> {unimplemented!()}

/// `a :: b`.
pub type Con<A, B> = App<Concat, Tup<A, B>>;
