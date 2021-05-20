/*

Demonstrates that most formation rules are lifted to Path Semantics.

*/

use prop::*;
use path_semantics::*;
use std::rc::Rc;
use Either::*;

//   a : T, b : T
// ---------------
// (a, b) : (T, U)
pub fn product_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
    ty_a: Imply<A, T>,
    ty_b: Imply<B, U>,
) -> Imply<And<A, B>, And<T, U>> {
    Rc::new(move |(a, b)| {
        (ty_a(a), ty_b(b))
    })
}

//   a : T, b : T
// ---------------
//  a | b : T | U
pub fn sum_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
    ty_a: Imply<A, T>,
    ty_b: Imply<B, U>,
) -> Imply<Or<A, B>, Or<T, U>> {
    Rc::new(move |or_a_b| {
        match or_a_b {
            Left(a) => Left(ty_a(a)),
            Right(b) => Right(ty_b(b)),
        }
    })
}

// a : T, f : T -> U
// -----------------
//     f(a) : U
pub fn app_formation<A: Prop, F: Prop, T: Prop, U: Prop>(
    ty_a: Imply<A, T>,
    ty_f: Imply<F, Imply<T, U>>,
) -> Imply<And<F, A>, U> {
    Rc::new(move |(f, a)| {
        ty_f(f)(ty_a(a))
    })
}

//        a : U
// ----------------------
// (\(_: T) = a) : T -> U
pub fn abs_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
    ty_a: Imply<A, U>,
    abs: Imply<And<A, Imply<A, U>>, Imply<B, Imply<T, U>>>,
) -> Imply<A, Imply<B, Imply<T, U>>> {
    Rc::new(move |a| abs((a, ty_a.clone())))
}

//    a : T, b : U
// -----------------
// (a = b) : (T = U)
pub fn eqv_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
    ty_a: Imply<A, T>,
    ty_b: Imply<B, U>,
) -> Imply<Eq<A, B>, Eq<T, U>>
    where A: POrd<T>, B: POrd<U>
{
    Rc::new(move |f| {
        let p = assume_naive();
        p((f, (ty_a.clone(), ty_b.clone())))
    })
}

fn main() {}
