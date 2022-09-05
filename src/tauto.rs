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
use quality::Q;

/// A tautological proposition.
pub type Tauto<A> = fn() -> A;

/// A paradoxical proposition.
pub type Para<A> = fn(A) -> False;

/// A uniform proposition.
pub type Uniform<A> = Or<Tauto<A>, Para<A>>;

/// A proposition is a theory when non-uniform.
pub type Theory<A> = Not<Uniform<A>>;

/// Lift equality with tautological distinction into quality.
pub fn lift_q<A: Prop, B: Prop>(
    eq_ab: Eq<A, B>,
    _: Theory<Eq<A, B>>
) -> Q<A, B> {Q(eq_ab)}

/// `(a ~~ b) ∧ (a == c)  =>  (c ~~ b)`.
pub fn q_in_left_arg<A: Prop, B: Prop, C: Prop>(f: Q<A, B>, g: Tauto<Eq<A, C>>) -> Q<C, B> {
    Q(eq::commute(eq::transitivity(eq::commute(quality::to_eq(f)), g())))
}

/// `(a ~~ b) ∧ (b == c)  =>  (a ~~ c)`.
pub fn q_in_right_arg<A: Prop, B: Prop, C: Prop>(f: Q<A, B>, g: Tauto<Eq<B, C>>) -> Q<A, C> {
    Q(eq::transitivity(quality::to_eq(f), g()))
}

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

/// `x => ¬¬x`.
pub fn not_double<A: Prop>(_: Tauto<A>) -> Tauto<Not<Not<A>>> {
    unimplemented!()
}

/// `(¬¬x == false) => (x == false)`.
pub fn para_not_double<A: Prop>(_: Para<Not<Not<A>>>) -> Para<A> {
    unimplemented!()
}

/// `(x == false) => (¬¬x == false)`.
pub fn para_not_rev_double<A: Prop>(_: Para<A>) -> Para<Not<Not<A>>> {
    unimplemented!()
}

/// `x == x`.
pub use eq::refl as eq_refl;

/// `((x == y) == true) => ((y == x) == true)`.
pub fn eq_symmetry<A: Prop, B: Prop>(_: Tauto<Eq<A, B>>) -> Tauto<Eq<B, A>> {
    unimplemented!()
}

/// `((x == y) == false) => ((y == x) == false)`.
pub fn neq_symmetry<A: Prop, B: Prop>(_: Para<Eq<A, B>>) -> Para<Eq<B, A>> {
    unimplemented!()
}

/// `(a == b) ∧ (b == c) => (a == c)`.
pub fn eq_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Eq<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Tauto<Eq<A, C>> {
    unimplemented!()
}

pub use eq_transitivity as eq_in_right_arg;

/// `(a == b) ∧ (a == c) => (c == b)`.
pub fn eq_in_left_arg<A: Prop, B: Prop, C: Prop>(
    f: Tauto<Eq<A, B>>,
    g: Tauto<Eq<A, C>>,
) -> Tauto<Eq<C, B>> {
    eq_transitivity(eq_symmetry(g), f)
}

/// `((a == b) == false) ∧ ((b == c) == true) => ((a == c) == false)`.
pub fn para_eq_transitivity_left<A: Prop, B: Prop, C: Prop>(
    _: Para<Eq<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Para<Eq<A, C>> {
    unimplemented!()
}

/// `((a == b) == true) ∧ ((b == c) == false) => ((a == c) == false)`.
pub fn para_eq_transitivity_right<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Eq<A, B>>,
    _: Para<Eq<B, C>>
) -> Para<Eq<A, C>> {
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

/// `uniform(a) => uniform(¬¬a)`.
pub fn uniform_not_double<A: Prop>(
    f: Uniform<A>
) -> Uniform<Not<Not<A>>> {
    match f {
        Left(x) => Left(not_double(x)),
        Right(x) => Right(para_not_rev_double(x)),
    }
}

/// `uniform(a == b) ∧ uniform(b == c) => uniform(a == c)`.
pub fn uniform_transitivity<A: Prop, B: Prop, C: Prop>(
    f: Uniform<Eq<A, B>>,
    g: Uniform<Eq<B, C>>
) -> Uniform<Eq<A, C>> {
    match (f, g) {
        (Left(t_ab), Left(t_bc)) => Left(eq_transitivity(t_ab, t_bc)),
        (Left(t_ab), Right(p_bc)) => Right(para_eq_transitivity_right(t_ab, p_bc)),
        (Right(p_ab), Left(t_bc)) => Right(para_eq_transitivity_left(p_ab, t_bc)),
        (Right(p_ab), Right(p_bc)) => uniform_from_para_transitivity(p_ab, p_bc),
    }
}

/// `((a == b) == false) ∧ ((b == c) == false) => uniform(a == c)`.
pub fn uniform_from_para_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Para<Eq<A, B>>,
    _: Para<Eq<B, C>>,
) -> Uniform<Eq<A, C>> {
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
