//! Tactics for Logical NOT.

#![allow(unreachable_code)]

use crate::*;

/// `a => ¬¬a`.
pub fn double<A: Prop>(a: A) -> Not<Not<A>> {
    Rc::new(move |x| x(a.clone()))
}

/// `¬¬a => a`.
pub fn rev_double<A: DProp>(f: Not<Not<A>>) -> A {
    rev_double_excm(f, A::decide())
}

/// `¬¬a => a`.
pub fn rev_double_excm<A: Prop>(f: Not<Not<A>>, excm: ExcM<A>) -> A {
    use Either::*;

    match excm {
        Left(a) => a,
        Right(not_a) => match f(not_a) {},
    }
}

/// `¬¬¬a => ¬a`.
pub fn rev_triple<A: Prop>(x: Not<Not<Not<A>>>) -> Not<A> {
    Rc::new(move |a| x(double(a)))
}

/// `¬a ⋀ a => b`.
pub fn absurd<A: Prop, B: Prop>(f: Not<A>, g: A) -> B {
    imply::absurd()(f(g))
}
