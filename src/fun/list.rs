//! List.

use super::*;
use natp::{FAdd, Nat, Succ, Zero};

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
/// `a : list(b)  =>  (a == nil{b}) ⋁ (a == cons{b}(head(a), tail(a)))`.
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
/// `∃ nil{a} : list(a) { x } ⋀ ∃ cons{a}(b, c) : list(a) { x }  =>  x`.
pub fn list_exists<A: Prop, B: VProp, C: VProp, X: Prop>(
    _: Exists<Ty<Nil<A>, List<A>>, X>,
    _: Exists<Ty<Cons<A, B, Nil<A>>, List<A>>, X>
) -> X {unimplemented!()}

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

/// `cons{x}(a, b)`.
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
/// `(nil{x} : list(x)) ⋀ (a : list(x))  =>  concat{x}(nil{x}, a) == a`.
pub fn concat_nil<X: Prop, A: Prop>(
    _ty_nil: Ty<Nil<X>, List<X>>,
    _ty_a: Ty<A, List<X>>
) -> Eq<Concat<X, Nil<X>, A>, A> {unimplemented!()}
/// `(cons{x}(a, b) : list(x)) ⋀ (c : list(x))  =>
///  concat{x}(cons{x}(a, b), c) == cons{x}(a, concat{x}(b, c))`.
pub fn concat_cons<X: Prop, A: Prop, B: Prop, C: Prop>(
    _ty_cons: Ty<Cons<X, A, B>, List<X>>,
    _ty_c: Ty<C, List<X>>
) -> Eq<Concat<X, Cons<X, A, B>, C>, Cons<X, A, Concat<X, B, C>>> {unimplemented!()}
/// `concat{x}[len{x}]  == add`.
pub fn norm1_concat_len<X: Prop>() -> Eq<SymNorm2<App<FConcat, X>, App<FLen, X>>, FAdd> {
    unimplemented!()
}

/// Length of list.
#[derive(Copy, Clone)]
pub struct FLen(());

/// `len{x}(a)`.
pub type Len<X, A> = App<App<FLen, X>, A>;

/// `(a : type(0))  =>  (len{a} : list(a) -> nat)`.
pub fn len_ty<A: Prop>(_a: Ty<A, Type<Z>>) -> Ty<App<FLen, A>, Pow<Nat, List<A>>> {
    unimplemented!()
}
/// `nil{a} : list(a)  =>  len(nil{a}) == 0`.
pub fn len_nil<A: Prop>(_: Ty<Nil<A>, List<A>>) -> Eq<Len<A, Nil<A>>, Zero> {unimplemented!()}
/// `cons{x}(a, b) : list(a)  =>  len{x}(cons{x}(a, b)) == succ(len{x}(b))`.
pub fn len_cons<X: Prop, A: Prop, B: Prop>(
    _: Ty<Cons<X, A, B>, List<A>>
) -> Eq<Len<X, Cons<X, A, B>>, Succ<Len<X, B>>> {
    unimplemented!()
}
