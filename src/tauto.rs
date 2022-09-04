//! # Tautological Propositions
//!
//! By using function pointers,
//! one can force construction of propositions
//! without capturing any variables,
//! such that the proposition is tautological true,
//! instead of just assuming it is true.
//!
//! Some theorems about tautological propositions
//! are true, even though they are impossible to code.
//!
//! For example, if you have a tautological equality `x == y`,
//! then you can construct the tautological symmetric equality `y == x`,
//! even though you don't have a concrete proof yet.
//!
//! By pretending that one can anyway,
//! one can make tautological theorem proving more powerful.

use crate::*;

/// A tautological proposition.
pub type Tauto<A> = fn() -> A;

/// A paradoxical proposition.
pub type Para<A> = fn(A) -> False;

/// A uniform proposition.
pub type Uniform<A> = Or<Tauto<A>, Para<A>>;

/// A proposition is a theory when non-uniform.
pub type Theory<A> = Not<Uniform<A>>;

/// `true => true`.
pub fn tr() -> True {True}

/// `false => false`.
pub fn fa(x: False) -> False {x}

/// A consistent logic can't prove `false` without further assumptions.
pub fn consistency() -> Not<Tauto<False>> {
    Rc::new(move |f| f())
}

/// `a => (a == true)`.
pub fn to_eq_true<A: Prop>(
    _: Tauto<A>
) -> Tauto<Eq<A, True>> {
    unimplemented!()
}

/// `(a == true) => a`.
pub fn from_eq_true<A: Prop>(
    _: Tauto<Eq<A, True>>
) -> Tauto<A> {
    unimplemented!()
}

/// `¬a => (a == false)`.
pub fn to_eq_false<A: Prop>(
    _: Para<A>
) -> Tauto<Eq<A, False>> {
    unimplemented!()
}

/// `(a == false) => ¬a`.
pub fn from_eq_false<A: Prop>(
    _: Tauto<Eq<A, False>>
) -> Para<A> {
    unimplemented!()
}

/// `x == x`.
pub fn eq_refl<A: Prop>() -> Tauto<Eq<A, A>> {eq::refl::<A>}

/// `(x == y) => (y == x)`.
pub fn eq_symmetry<A: Prop, B: Prop>(_: Tauto<Eq<A, B>>) -> Tauto<Eq<B, A>> {
    unimplemented!()
}

/// `(a == b) ∧ (b == c) => (a == c)`.
pub fn eq_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Eq<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Tauto<Eq<A, C>> {
    unimplemented!()
}

/// `x => x`.
pub fn imply_refl<A: Prop>() -> Tauto<Imply<A, A>> {
    fn inner<A: Prop>() -> Imply<A, A> {Rc::new(move |x| x)}
    inner::<A>
}

/// `(a => b) ∧ (b => c) => (a => c)`.
pub fn imply_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Imply<B, C>>,
) -> Tauto<Imply<A, C>> {
    unimplemented!()
}

/// `(a ∧ b) => (a == b)`.
pub fn and_to_eq_pos<A: Prop, B: Prop>(_: Tauto<A>, _: Tauto<B>) -> Tauto<Eq<A, B>> {
    unimplemented!()
}

/// `(a == true) => ((a ⋁ b) == true)`.
pub fn or_left<A: Prop, B: Prop>(
    _: Tauto<A>
) -> Tauto<Or<A, B>> {
    unimplemented!()
}

/// `(b == true) => ((a ⋁ b) == true)`.
pub fn or_right<A: Prop, B: Prop>(
    _: Tauto<B>
) -> Tauto<Or<A, B>> {
    unimplemented!()
}

/// `(a == false) ∧ (b == false) => ((a ⋁ b) == false)`.
pub fn or_para<A: Prop, B: Prop>(
    _: Para<A>,
    _: Para<B>
) -> Para<Or<A, B>> {
    unimplemented!()
}

/// `((a ⋁ b) == false) => (a == false) ∧ (b == false)`.
pub fn rev_or_para<A: Prop, B: Prop>(
    _: Para<Or<A, B>>,
) -> And<Para<A>, Para<B>> {
    unimplemented!()
}

/// `((a ∧ b) == false) => (a == false) ⋁ (b == false)`.
pub fn para_or<A: Prop, B: Prop>(
    _: Para<And<A, B>>
) -> Or<Para<A>, Para<B>> {
    unimplemented!()
}

/// `(a == true) ∧ (b == true) => ((a ∧ b) == true)`.
pub fn and<A: Prop, B: Prop>(
    _: Tauto<A>,
    _: Tauto<B>,
) -> Tauto<And<A, B>> {
    unimplemented!()
}

/// `((a ∧ b) == true) => (a == true) ∧ (b == true)`.
pub fn rev_and<A: Prop, B: Prop>(
    _: Tauto<And<A, B>>,
) -> And<Tauto<A>, Tauto<B>> {
    unimplemented!()
}

/// `(a == false) => ((a ∧ b) == false)`.
pub fn and_para_left<A: Prop, B: Prop>(
    _: Para<A>,
) -> Para<And<A, B>> {
    unimplemented!()
}

/// `(b == false) => ((a ∧ b) == false)`.
pub fn and_para_right<A: Prop, B: Prop>(
    _: Para<B>,
) -> Para<And<A, B>> {
    unimplemented!()
}

/// `(a => b) ∧ (a == c)  =>  (c => b)`.
pub fn imply_in_left_arg<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Eq<A, C>>
) -> Tauto<Imply<C, B>> {
    unimplemented!()
}

/// `(a => b) ∧ (b == c)  =>  (a => c)`.
pub fn imply_in_right_arg<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Tauto<Imply<A, C>> {
    unimplemented!()
}

/// If something is provable from a tautology,
/// then it is provable without the tautology.
pub fn imply_reduce_left_arg<A: Prop, B: Prop>(
    _: Imply<Tauto<A>, B>
) -> B {
    unimplemented!()
}

/// `uniform(a) ∧ uniform(b) => uniform(a ∧ b)`.
pub fn uniform_and<A: Prop, B: Prop>(
    _: Uniform<A>,
    _: Uniform<B>
) -> Uniform<And<A, B>> {
    unimplemented!()
}

/// `uniform(a ∧ b) => uniform(a) ∧ uniform(b)`.
pub fn rev_uniform_and<A: Prop, B: Prop>(
    _: Uniform<And<A, B>>,
) -> And<Uniform<A>, Uniform<B>> {
    unimplemented!()
}

/// `uniform(a ∧ b) => uniform(a ⋁ b)`.
pub fn uniform_and_to_or<A: Prop, B: Prop>(
    _: Uniform<And<A, B>>,
) -> Uniform<Or<A, B>> {
    unimplemented!()
}

/// `uniform(a) => (a ⋁ ¬a)`.
pub fn uniform_to_excm<A: Prop>(
    _: Uniform<A>
) -> Tauto<ExcM<A>> {
    unimplemented!()
}

/// `(a ⋁ ¬a) => uniform(a)`.
pub fn excm_to_uniform<A: Prop>(
    _: Tauto<ExcM<A>>
) -> Uniform<A> {
    unimplemented!()
}

/// `(a => b) ∧ a  =>  b`.
pub fn modus_ponens<A: Prop, B: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<A>,
) -> Tauto<B> {
    unimplemented!()
}

/// `theory(a) ⋀ theory(b) => theory(a ⋀ b)`.
pub fn theory_and<A: Prop, B: Prop>(
    f: Theory<A>,
    g: Theory<B>
) -> Theory<And<A, B>> {
    Rc::new(move |uni| match uni {
        Left(t_ab) => f(Left(rev_and(t_ab).0)),
        Right(p_ab) => match para_or(p_ab) {
            Left(p_a) => f(Right(p_a)),
            Right(p_b) => g(Right(p_b)),
        }
    })
}
