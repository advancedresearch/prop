/*

Demonstrates a bit Boolean algebra formalised with Path Semantics.

*/

use prop::*;
use path_semantics::*;
use nat::*;
use std::rc::Rc;
use Either::*;

// bool : type
// false : bool
// true : bool
pub trait DeclBool<Type: LProp<N = S<S<N>>>, N: Nat> {
    type Bool: LProp<N = S<N>>;
    type False: LProp<N = N> + POrd<Self::False> + POrd<Self::True>;
    type True: LProp<N = N> + POrd<Self::True> + POrd<Self::False>;
    fn ty_bool() -> Imply<Self::Bool, Type>;
    fn ty_false() -> Imply<Self::False, Self::Bool>;
    fn ty_true() -> Imply<Self::True, Self::Bool>;
    unsafe fn const_false() -> Self::False;
    unsafe fn const_true() -> Self::True;
    fn decide<X: LProp>() -> Or<Q<X, Self::False>, Q<X, Self::True>>;
}

/// Links two memory slots.
pub struct Mem<T: LProp>(Imply<T, Inc<T>>);

impl<T: LProp> Mem<T> {
    /// Accesses memory.
    pub fn read(self) -> Imply<T, Inc<T>> {self.0}
}

/// Function type.
#[derive(Clone)]
pub struct FnTy<T, U>(pub Imply<T, U>);

// (T -> U) : type
pub trait DeclFn<Type: LProp> {
    fn ty_fn<T: Prop, U: Prop>() -> Imply<FnTy<T, U>, Type>;
}

// idb : bool -> bool
// not : bool -> bool
// false1 : bool -> bool
// true1 : bool -> bool
pub trait DeclBool1<Type: LProp<N = S<S<N>>>, N: Nat>: DeclBool<Type, N> + DeclFn<Type> {
    type Idb: LProp<N = N>;
    type Not: LProp<N = N>;
    type False1: LProp<N = N>;
    type True1: LProp<N = N>;
    fn ty_idb() -> Imply<Self::Idb, FnTy<Self::Bool, Self::Bool>>;
    fn ty_not() -> Imply<Self::Not, FnTy<Self::Bool, Self::Bool>>;
    fn ty_false1() -> Imply<Self::False1, FnTy<Self::Bool, Self::Bool>>;
    fn ty_true1() -> Imply<Self::True1, FnTy<Self::Bool, Self::Bool>>;

    fn def_idb<X: LProp>(_idb: Self::Idb, f: Mem<X>) -> And<
        Imply<Q<X, Self::False>, Q<Inc<X>, Self::False>>,
        Imply<Q<X, Self::True>, Q<Inc<X>, Self::True>>,
    >
        where X: POrd<Inc<X>>
    {
        let f1 = f.0.clone();
        let f2 = f.0.clone();
        (Rc::new(move |eq_x_false| {
            let p = assume_naive();
            p((eq_x_false, (f1.clone(), imply::id())))
        }),
         Rc::new(move |eq_x_true| {
             let p = assume_naive();
             p((eq_x_true, (f2.clone(), imply::id())))
         })
        )
    }

    fn def_not<X: LProp>(_not: Self::Not, f: Mem<X>) -> And<
        Imply<Q<X, Self::False>, Q<Inc<X>, Self::True>>,
        Imply<Q<X, Self::True>, Q<Inc<X>, Self::False>>,
    >
        where X: POrd<Inc<X>>
    {
        let f = f.read();
        let f1 = f.clone();
        let f2 = f.clone();
        (Rc::new(move |eq_x_false| {
            let p = assume_naive();
            p((eq_x_false, (f1.clone(), unsafe {Self::const_true().map_any()})))
        }),
         Rc::new(move |eq_x_true| {
             let p = assume_naive();
             p((eq_x_true, (f2.clone(), unsafe {Self::const_false().map_any()})))
         })
        )
    }

    fn def_false1<X: LProp>(_false1: Self::False1, f: Imply<X, Inc<X>>) -> And<
        Imply<Q<X, Self::False>, Q<Inc<X>, Self::False>>,
        Imply<Q<X, Self::True>, Q<Inc<X>, Self::False>>,
    >
        where X: POrd<Inc<X>>
    {
        let f1 = f.clone();
        let f2 = f.clone();
        (Rc::new(move |eq_x_false| {
            let p = assume_naive();
            p((eq_x_false, (f1.clone(), unsafe {Self::const_false().map_any()})))
        }),
         Rc::new(move |eq_x_true| {
             let p = assume_naive();
             p((eq_x_true, (f2.clone(), unsafe {Self::const_false().map_any()})))
         })
        )
    }

    fn def_true1<X: LProp>(_true1: Self::True1, f: Imply<X, Inc<X>>) -> And<
        Imply<Q<X, Self::False>, Q<Inc<X>, Self::True>>,
        Imply<Q<X, Self::True>, Q<Inc<X>, Self::True>>,
    >
        where X: POrd<Inc<X>>
    {
        let f1 = f.clone();
        let f2 = f.clone();
        (Rc::new(move |eq_x_false| {
            let p = assume_naive();
            p((eq_x_false, (f1.clone(), unsafe {Self::const_true().map_any()})))
        }),
         Rc::new(move |eq_x_true| {
             let p = assume_naive();
             p((eq_x_true, (f2.clone(), unsafe {Self::const_true().map_any()})))
         })
        )
    }
}

pub fn proof<T: DeclBool1<Type, Zero>, X: LProp<N = Zero>, Type: LProp<N = Two>>(
    f1: Mem<X>,
    f2: Mem<X>,
    idb: T::Idb,
    not: T::Not,
    eq_x_true: Q<X, T::True>,
) -> And<Q<Inc<X>, T::True>, Q<Inc<X>, T::False>>
    where X: POrd<Inc<X>>
{
    let idb_expr = T::def_idb(idb, f1);
    let not_expr = T::def_not(not, f2);
    (idb_expr.1(eq_x_true.clone()), not_expr.1(eq_x_true.clone()))
}

pub fn proof2<T: DeclBool1<Type, Zero>, X: LProp<N = Zero>, Type: LProp<N = Two>>(
    f1: Mem<X>,
    f2: Mem<Inc<X>>,
    idb: T::Idb,
    not: T::Not,
    eq_x_true: Q<X, T::True>,
) -> Q<Inc<Inc<X>>, T::False>
    where X: POrd<Inc<X>>,
          Inc<X>: POrd<Inc<Inc<X>>>
{
    let idb_expr = T::def_idb(idb, f1);
    let not_expr = T::def_not(not, f2);
    let x2 = idb_expr.1(eq_x_true.clone());
    not_expr.1(x2)
}

pub fn proof3<
    T: DeclBool1<Type, Zero>,
    X: LProp<N = Zero>,
    Type: LProp<N = Two>
>(
    f1: Mem<X>,
    f2: Mem<Inc<X>>,
    not: T::Not,
)
    where X: POrd<Inc<X>>,
          Inc<X>: POrd<Inc<Inc<X>>>
{
    let not_expr = T::def_not(not.clone(), f1);
    let not_expr2 = T::def_not(not, f2);
    match T::decide() {
        Left(eq_x_false) => {
            let x1 = not_expr.0(eq_x_false);
            let x2 = not_expr2.1(x1);
            check_q::<T::False, _>(x2)
        }
        Right(eq_x_true) => {
            let x1 = not_expr.1(eq_x_true);
            let x2 = not_expr2.0(x1);
            check_q::<T::True, _>(x2)
        }
    }
}

fn main() {}
