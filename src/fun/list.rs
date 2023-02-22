//! List.

use super::*;

/// A list.
#[derive(Copy, Clone)]
pub struct FList(());

/// `list(a)`.
pub type List<A> = App<FList, A>;

/// `head(a)`.
pub struct Head<A>(A);

/// `tail(a)`.
pub struct Tail<A>(A);

/// `(a : type(0))  =>  (list : a -> type(0))`.
pub fn list_ty<A: Prop>(_a_ty: Ty<A, Type<Z>>) -> Ty<FList, Pow<Type<Z>, A>> {unimplemented!()}
/// `a : list(b)  =>  (a == nil{b}) ⋁ (a == (head(a) :: tail(a)))`
pub fn list_def<A: Prop, B: Prop>(
    _: Ty<A, List<B>>
) -> Or<Eq<A, Nil<B>>, Eq<A, Cons<B, Head<A>, Tail<A>>>> {
    unimplemented!()
}
/// `(a : list(b)) ⋀ ¬(a == nil{b})  =>  head(a) : b`.
pub fn head_ty<A: Prop, B: Prop>(_: Ty<A, List<B>>, _: Not<Eq<A, Nil<B>>>) -> Ty<Head<A>, B> {
    unimplemented!()
}
/// `(a : list(b)) ⋀ ¬(a == nil{b})  =>  tail(a) : list(b)`.
pub fn tail_ty<A: Prop, B: Prop>(
    _: Ty<A, List<B>>,
    _: Not<Eq<A, Nil<B>>>
) -> Ty<Tail<A>, List<B>> {
    unimplemented!()
}

/// An empty list.
#[derive(Copy, Clone)]
pub struct FNil(());

/// `nil{a}`.
pub type Nil<A> = App<FNil, A>;

/// `(a : type(0))  =>  (nil{a} : list(a))`.
pub fn nil_ty<A: Prop>(_a_ty: Ty<A, Type<Z>>) -> Ty<Nil<A>, List<A>> {unimplemented!()}

/// A non-empty list.
#[derive(Copy, Clone)]
pub struct FCons(());

/// `const{x}(a, b)`.
pub type Cons<X, A, B> = App<App<FCons, X>, Tup<A, B>>;

/// `a : type(0)  =>  cons{a} : (a, list(a)) -> list(a)`.
pub fn cons_ty<A: Prop>() -> Ty<App<FCons, A>, Pow<List<A>, Tup<A, List<A>>>> {
    unimplemented!()
}

/// List concatenation.
#[derive(Copy, Clone)]
pub struct FConcat(());

/// `concat{x}(a, b)`.
pub type Concat<X, A, B> = App<App<FConcat, X>, Tup<A, B>>;

/// `(a : type(0))  =>  (concat{a} : (list(a), list(a)) -> list(a))`.
pub fn concat_ty<A: Prop>(
    _a_ty: Ty<A, Type<Z>>
) -> Ty<App<FConcat, A>, Pow<List<A>, Tup<List<A>, List<A>>>> {unimplemented!()}
