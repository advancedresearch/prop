//! Tactics for Logical IMPLY.

use crate::*;

/// `a => b  =>  ¬b => ¬a`.
///
/// Swap sides of implication by taking their negation.
pub fn modus_tollens<A: Prop, B: Prop>(f: Imply<A, B>) -> Imply<Not<B>, Not<A>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| match x(f(y)) {})
    })
}

/// `a => b ∧ b => c  =>  a => c`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    f: Imply<A, B>,
    g: Imply<B, C>,
) -> Imply<A, C> {
    Rc::new(move |x| g(f(x)))
}

/// `(a => b) ∧ a  =>  b`
pub fn modus_ponens<A: Prop, B: Prop>(
    f: Imply<A, B>,
    a: A,
) -> B {
    f(a)
}

/// `a => (b => c)  =>  b => (a => c)`
pub fn reorder_args<A: Prop, B: Prop, C: Prop>(
    f: Imply<A, Imply<B, C>>
) -> Imply<B, Imply<A, C>> {
    Rc::new(move |x| {
        let f = f.clone();
        Rc::new(move |y| f(y)(x))
    })
}

/// `(a => b) ∧ a  =>  ¬¬a => ¬¬b`.
pub fn double_neg<A: Prop, B: Prop>(f: Imply<A, B>, a: A) -> Imply<Not<Not<A>>, Not<Not<B>>> {
    let g = a.double_neg();
    Rc::new(move |x| not::double(f(g(x))))
}

/// `(¬¬a => ¬¬b) ∧ b  =>  a => b`.
pub fn rev_double_neg<A: Prop, B: Prop>(f: Imply<Not<Not<A>>, Not<Not<B>>>, b: B) -> Imply<A, B> {
    let g = b.double_neg();
    Rc::new(move |x| g(f(not::double(x))))
}

/// `(a => b) => (¬a ∨ b)`.
pub fn to_or<A: Prop, B: Prop>(f: Imply<A, B>) -> Or<Not<A>, B> {
    use Either::*;

    let a = <A as Decidable>::decide();
    let b = <B as Decidable>::decide();
    match (a, b) {
        (_, Left(b)) => Right(b),
        (Left(a), _) => Right(f(a)),
        (Right(a), _) => Left(a.clone()),
    }
}
