//! Tactics for Logical NOT.

use crate::*;

/// `a => ¬¬a`.
pub fn double<A: Prop>(a: A) -> Not<Not<A>> {
    Rc::new(move |x| x(a.clone()))
}

/// `¬¬a => a`.
pub fn rev_double<A: DProp>(f: Not<Not<A>>) -> A {
    use Either::*;

    match A::decide() {
        Left(a) => a,
        Right(not_a) => match f(not_a) {},
    }
}
