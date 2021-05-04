//! Tactics for Logical NOT.

use crate::*;

/// `a => ¬¬a`.
pub fn double<A: Prop>(a: A) -> Not<Not<A>> {
    Rc::new(move |x| x(a))
}
