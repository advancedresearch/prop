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
use qubit::Qu;

/// `a^b`.
pub type Pow<A, B> = fn(B) -> A;

#[marker]
/// Implemented by exponential propositions.
pub trait PowImply<A, B>: Fn(A) -> B {}

impl<A> PowImply<A, True> for Pow<True, A> {}
impl<A> PowImply<False, A> for Pow<A, False> {}
impl<A> PowImply<True, Eq<A, A>> for Pow<Eq<A, A>, True> {}
impl<A, B> PowImply<Pow<Not<A>, B>, Not<Pow<A, B>>>
    for Pow<Not<Pow<A, B>>, Pow<Not<A>, B>> {}
impl<A, B> PowImply<Not<Pow<A, B>>, Pow<Not<A>, B>>
    for Pow<Pow<Not<A>, B>, Not<Pow<A, B>>> {}
impl<A, B, C> PowImply<Pow<And<A, B>, C>, And<Pow<A, C>, Pow<B, C>>>
    for Pow<And<Pow<A, C>, Pow<B, C>>, Pow<And<A, B>, C>> {}
impl<A, B, C> PowImply<And<Pow<A, C>, Pow<B, C>>, Pow<And<A, B>, C>>
    for Pow<Pow<And<A, B>, C>, And<Pow<A, C>, Pow<B, C>>> {}
impl<A, B, C> PowImply<Pow<Or<A, B>, C>, Or<Pow<A, C>, Pow<B, C>>>
    for Pow<Or<Pow<A, C>, Pow<B, C>>, Pow<Or<A, B>, C>> {}
impl<A, B, C> PowImply<Or<Pow<A, C>, Pow<B, C>>, Pow<Or<A, B>, C>>
    for Pow<Pow<Or<A, B>, C>, Or<Pow<A, C>, Pow<B, C>>> {}
impl<A, B, C> PowImply<Pow<Eq<A, B>, C>, Eq<Pow<A, C>, Pow<B, C>>>
    for Pow<Eq<Pow<A, C>, Pow<B, C>>, Pow<Eq<A, B>, C>> {}
impl<A, B, C> PowImply<Eq<Pow<A, C>, Pow<B, C>>, Pow<Eq<A, B>, C>>
    for Pow<Pow<Eq<A, B>, C>, Eq<Pow<A, C>, Pow<B, C>>> {}
impl<A, B, C> PowImply<Pow<Imply<A, B>, C>, Imply<Pow<A, C>, Pow<B, C>>>
    for Pow<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>> {}
impl<A, B, C> PowImply<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>>
    for Pow<Pow<Imply<A, B>, C>, Imply<Pow<A, C>, Pow<B, C>>> {}
impl<A, B, C> PowImply<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>>
    for Pow<Or<Pow<C, A>, Pow<C, B>>, Pow<C, And<A, B>>> {}
impl<A, B, C> PowImply<Or<Pow<C, A>, Pow<C, B>>, Pow<C, And<A, B>>>
    for Pow<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>> {}
impl<A, B, C> PowImply<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>>
    for Pow<And<Pow<C, A>, Pow<C, B>>, Pow<C, Or<A, B>>> {}
impl<A, B, C> PowImply<And<Pow<C, A>, Pow<C, B>>, Pow<C, Or<A, B>>>
    for Pow<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>> {}
impl<A, B, C> PowImply<Pow<C, Eq<A, B>>, Eq<Pow<C, A>, Pow<C, B>>>
    for Pow<Eq<Pow<C, A>, Pow<C, B>>, Pow<C, Eq<A, B>>> {}
impl<A, B, C> PowImply<Eq<Pow<C, A>, Pow<C, B>>, Pow<C, Eq<A, B>>>
    for Pow<Pow<C, Eq<A, B>>, Eq<Pow<C, A>, Pow<C, B>>> {}

/// Get instance of exponential proposition.
pub fn pow<A: Prop, B: Prop>() -> Pow<A, B>
    where Pow<A, B>: PowImply<B, A>
{unimplemented!()}

/// Get tautological proposition.
pub fn tauto<A: Prop>() -> Tauto<A>
    where Tauto<A>: PowImply<True, A>
{pow()}

/// Get paradoxical proposition.
pub fn para<A: Prop>() -> Para<A>
    where Para<A>: PowImply<A, False>
{pow()}

/// `(¬(a^b))^((¬a)^b)`.
pub fn hooo_not<A: Prop, B: Prop>()
-> Pow<Not<Pow<A, B>>, Pow<Not<A>, B>> {pow()}

/// `((¬a)^b)^(¬(a^b))`.
pub fn hooo_rev_not<A: Prop, B: Prop>()
-> Pow<Pow<Not<A>, B>, Not<Pow<A, B>>> {pow()}

/// `(a^c ⋀ b^c)^((a ⋀ b)^c)`.
pub fn hooo_and<A: Prop, B: Prop, C: Prop>()
-> Pow<And<Pow<A, C>, Pow<B, C>>, Pow<And<A, B>, C>> {pow()}

/// `((a ⋀ b)^c)^(a^c ⋀ b^c)`.
pub fn hooo_rev_and<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<And<A, B>, C>, And<Pow<A, C>, Pow<B, C>>> {pow()}

/// `(c^a ⋁ c^b)^(c^(a ⋀ b))`.
pub fn hooo_dual_and<A: Prop, B: Prop, C: Prop>()
-> Pow<Or<Pow<C, A>, Pow<C, B>>, Pow<C, And<A, B>>> {pow()}

/// `(c^(a ⋀ b))^(c^a ⋁ c^b)`.
pub fn hooo_dual_rev_and<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>> {pow()}

/// `(a^c ⋁ b^c)^((a ⋁ b)^c)`.
pub fn hooo_or<A: Prop, B: Prop, C: Prop>()
-> Pow<Or<Pow<A, C>, Pow<B, C>>, Pow<Or<A, B>, C>> {pow()}

/// `((a ⋁ b)^c)^(a^c ⋁ b^c)`.
pub fn hooo_rev_or<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<Or<A, B>, C>, Or<Pow<A, C>, Pow<B, C>>> {pow()}

/// `(c^a ⋀ c^b)^(c^(a ⋁ b))`.
pub fn hooo_dual_or<A: Prop, B: Prop, C: Prop>()
-> Pow<And<Pow<C, A>, Pow<C, B>>, Pow<C, Or<A, B>>> {pow()}

/// `(c^(a ⋁ b))^(c^a ⋀ c^b)`.
pub fn hooo_dual_rev_or<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>> {pow()}

/// `(a^c == b^c)^((a == b)^c)`.
pub fn hooo_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Eq<Pow<A, C>, Pow<B, C>>, Pow<Eq<A, B>, C>> {pow()}

/// `((a == b)^c)^(a^c == b^c)`.
pub fn hooo_rev_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<Eq<A, B>, C>, Eq<Pow<A, C>, Pow<B, C>>> {pow()}

/// `(c^a == c^b)^(c^(a == b))`.
pub fn hooo_dual_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Eq<Pow<C, A>, Pow<C, B>>, Pow<C, Eq<A, B>>> {pow()}

/// `(c^(a == b))^(c^a == c^b)`.
pub fn hooo_dual_rev_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<C, Eq<A, B>>, Eq<Pow<C, A>, Pow<C, B>>> {pow()}

/// `(a^c => b^c)^((a => b)^c)`.
pub fn hooo_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>> {pow()}

/// `((a => b)^c)^(a^c => b^c)`.
pub fn hooo_rev_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<Imply<A, B>, C>, Imply<Pow<A, C>, Pow<B, C>>> {pow()}

/// A tautological proposition.
pub type Tauto<A> = fn(True) -> A;

/// A paradoxical proposition.
pub type Para<A> = fn(A) -> False;

/// A uniform proposition.
pub type Uniform<A> = Or<Tauto<A>, Para<A>>;

/// A proposition is a theory when non-uniform.
pub type Theory<A> = Not<Uniform<A>>;

/// Lift equality with tautological distinction into quality.
pub fn lift_q<A: Prop, B: Prop>(
    _: Eq<A, B>,
    _: Theory<Eq<A, B>>
) -> Q<A, B> {unimplemented!()}

/// `~a ∧ (a == b)^true  =>  ~b`.
pub fn qu_in_arg<A: Prop, B: Prop>(_: Qu<A>, _: Tauto<Eq<A, B>>) -> Qu<B> {
    unimplemented!()
}

/// `(a ~~ b) ∧ (a == c)^true  =>  (c ~~ b)`.
pub fn q_in_left_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, qu_b)): Q<A, B>,
    g: Tauto<Eq<A, C>>
) -> Q<C, B> {
    (eq::in_left_arg(eq_ab, g(True)), (qu_in_arg(qu_a, g), qu_b))
}

/// `(a ~~ b) ∧ (b == c)^true  =>  (a ~~ c)`.
pub fn q_in_right_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, qu_b)): Q<A, B>,
    g: Tauto<Eq<B, C>>
) -> Q<A, C> {
    (eq::in_right_arg(eq_ab, g(True)), (qu_a, qu_in_arg(qu_b, g)))
}

/// `true^true`.
pub fn tr() -> Pow<True, True> {tauto()}

/// `false^false`.
pub fn fa() -> Pow<False, False> {para()}

/// A consistent logic can't prove `false` without further assumptions.
pub fn consistency() -> Not<Tauto<False>> {
    Rc::new(move |f| f(True))
}

/// `a^true => (a == true)^true`.
pub fn tauto_to_eq_true<A: Prop>(
    _: Tauto<A>
) -> Tauto<Eq<A, True>> {
    unimplemented!()
}

/// `(a == true)^true => a^true`.
pub fn tauto_from_eq_true<A: Prop>(
    _: Tauto<Eq<A, True>>
) -> Tauto<A> {
    unimplemented!()
}

/// `false^a => (a == false)^true`.
pub fn para_to_eq_false<A: Prop>(
    _: Para<A>
) -> Tauto<Eq<A, False>> {
    unimplemented!()
}

/// `(a == false)^true => false^a`.
pub fn para_from_eq_false<A: Prop>(
    _: Tauto<Eq<A, False>>
) -> Para<A> {
    unimplemented!()
}

/// `¬(x^true) => (¬x)^true`.
pub fn tauto_not<A: Prop>(_: Not<Tauto<A>>) -> Tauto<Not<A>> {
    unimplemented!()
}

/// `(¬x)^true => ¬(x^true)`.
pub fn tauto_rev_not<A: Prop>(_: Tauto<Not<A>>) -> Not<Tauto<A>> {
    unimplemented!()
}

/// `x^true => (¬¬x)^true`.
pub fn tauto_not_double<A: Prop>(_: Tauto<A>) -> Tauto<Not<Not<A>>> {
    unimplemented!()
}

/// `false^(¬¬x) => false^x`.
pub fn para_rev_not_double<A: Prop>(_: Para<Not<Not<A>>>) -> Para<A> {
    unimplemented!()
}

/// `false^x => false^(¬¬x)`.
///
/// The reason this is possible, is due to `(¬¬¬a => ¬a)^true`.
pub fn para_not_double<A: Prop>(_: Para<A>) -> Para<Not<Not<A>>> {
    unimplemented!()
}

/// `x == x`.
pub fn eq_refl<A: Prop>() -> Tauto<Eq<A, A>> {tauto()}

/// `((x == y) == true) => ((y == x) == true)`.
pub fn tauto_eq_symmetry<A: Prop, B: Prop>(_: Tauto<Eq<A, B>>) -> Tauto<Eq<B, A>> {
    unimplemented!()
}

/// `((x == y) == false) => ((y == x) == false)`.
pub fn para_eq_symmetry<A: Prop, B: Prop>(_: Para<Eq<A, B>>) -> Para<Eq<B, A>> {
    unimplemented!()
}

/// `(a == b) ∧ (b == c) => (a == c)`.
pub fn tauto_eq_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Eq<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Tauto<Eq<A, C>> {
    unimplemented!()
}

pub use tauto_eq_transitivity as tauto_eq_in_right_arg;

/// `(a == b) ∧ (a == c) => (c == b)`.
pub fn tauto_eq_in_left_arg<A: Prop, B: Prop, C: Prop>(
    f: Tauto<Eq<A, B>>,
    g: Tauto<Eq<A, C>>,
) -> Tauto<Eq<C, B>> {
    tauto_eq_transitivity(tauto_eq_symmetry(g), f)
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
pub fn imply_refl<A: Prop>() -> Imply<A, A> {
    Rc::new(move |x| x)
}

/// `(a => b) ∧ (b => c) => (a => c)`.
pub fn tauto_imply_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Imply<B, C>>,
) -> Tauto<Imply<A, C>> {
    unimplemented!()
}

/// `(a ∧ b) => (a == b)`.
pub fn tauto_and_to_eq_pos<A: Prop, B: Prop>(_: Tauto<A>, _: Tauto<B>) -> Tauto<Eq<A, B>> {
    unimplemented!()
}

/// `(a == true) => ((a ⋁ b) == true)`.
pub fn tauto_left_or<A: Prop, B: Prop>(
    _: Tauto<A>
) -> Tauto<Or<A, B>> {
    unimplemented!()
}

/// `(b == true) => ((a ⋁ b) == true)`.
pub fn tauto_right_or<A: Prop, B: Prop>(
    _: Tauto<B>
) -> Tauto<Or<A, B>> {
    unimplemented!()
}

/// `(a^true ⋁ b^true) => (a ⋁ b)^true`.
pub fn tauto_or<A: Prop, B: Prop>(or_ab: Or<Tauto<A>, Tauto<B>>) -> Tauto<Or<A, B>> {
    match or_ab {
        Left(tauto_a) => tauto_left_or(tauto_a),
        Right(tauto_b) => tauto_right_or(tauto_b),
    }
}

/// `(a ⋁ b)^true => (a^true ⋁ b^true)`.
pub fn tauto_rev_or<A: Prop, B: Prop>(_: Tauto<Or<A, B>>) -> Or<Tauto<A>, Tauto<B>> {
    unimplemented!()
}

/// `(a == false) ∧ (b == false) => ((a ⋁ b) == false)`.
pub fn para_to_or<A: Prop, B: Prop>(
    _: Para<A>,
    _: Para<B>
) -> Para<Or<A, B>> {
    unimplemented!()
}

/// `((a ⋁ b) == false) => (a == false) ∧ (b == false)`.
pub fn para_from_or<A: Prop, B: Prop>(
    _: Para<Or<A, B>>,
) -> And<Para<A>, Para<B>> {
    unimplemented!()
}

/// `((a ∧ b) == false) => (a == false) ⋁ (b == false)`.
pub fn para_and_to_or<A: Prop, B: Prop>(
    _: Para<And<A, B>>
) -> Or<Para<A>, Para<B>> {
    unimplemented!()
}

/// `(a == true) ∧ (b == true) => ((a ∧ b) == true)`.
pub fn tauto_and<A: Prop, B: Prop>(
    _: Tauto<A>,
    _: Tauto<B>,
) -> Tauto<And<A, B>> {
    unimplemented!()
}

/// `((a ∧ b) == true) => (a == true) ∧ (b == true)`.
pub fn tauto_rev_and<A: Prop, B: Prop>(
    _: Tauto<And<A, B>>,
) -> And<Tauto<A>, Tauto<B>> {
    unimplemented!()
}

/// `(a == false) => ((a ∧ b) == false)`.
pub fn para_left_and<A: Prop, B: Prop>(
    _: Para<A>,
) -> Para<And<A, B>> {
    unimplemented!()
}

/// `(b == false) => ((a ∧ b) == false)`.
pub fn para_right_and<A: Prop, B: Prop>(
    _: Para<B>,
) -> Para<And<A, B>> {
    unimplemented!()
}

/// `(a => b) ∧ (a == c)  =>  (c => b)`.
pub fn tauto_imply_in_left_arg<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Eq<A, C>>
) -> Tauto<Imply<C, B>> {
    unimplemented!()
}

/// `(a => b) ∧ (b == c)  =>  (a => c)`.
pub fn tauto_imply_in_right_arg<A: Prop, B: Prop, C: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<Eq<B, C>>
) -> Tauto<Imply<A, C>> {
    unimplemented!()
}

/// `(a => b) ∧ a  =>  b`.
pub fn tauto_modus_ponens<A: Prop, B: Prop>(
    _: Tauto<Imply<A, B>>,
    _: Tauto<A>,
) -> Tauto<B> {
    unimplemented!()
}

/// `uniform(a) => uniform(¬¬a)`.
pub fn uniform_not_double<A: Prop>(
    f: Uniform<A>
) -> Uniform<Not<Not<A>>> {
    match f {
        Left(x) => Left(tauto_not_double(x)),
        Right(x) => Right(para_not_double(x)),
    }
}

/// `uniform(a == a)`.
pub fn uniform_refl<A: Prop>() -> Uniform<Eq<A, A>> {
    Left(eq_refl())
}

/// `uniform(a == b) => uniform(b == a)`.
pub fn uniform_symmetry<A: Prop, B: Prop>(
    f: Uniform<Eq<A, B>>
) -> Uniform<Eq<B, A>> {
    match f {
        Left(t_ab) => Left(tauto_eq_symmetry(t_ab)),
        Right(p_ab) => Right(para_eq_symmetry(p_ab)),
    }
}

/// `uniform(a == b) ∧ uniform(b == c) => uniform(a == c)`.
pub fn uniform_transitivity<A: Prop, B: Prop, C: Prop>(
    f: Uniform<Eq<A, B>>,
    g: Uniform<Eq<B, C>>
) -> Uniform<Eq<A, C>> {
    match (f, g) {
        (Left(t_ab), Left(t_bc)) => Left(tauto_eq_transitivity(t_ab, t_bc)),
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
pub fn uniform_rev_and<A: Prop, B: Prop>(
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
pub fn uniform_from_excm<A: Prop>(
    _: Tauto<ExcM<A>>
) -> Uniform<A> {
    unimplemented!()
}

/// `theory(a) ⋀ theory(b) => theory(a ⋀ b)`.
pub fn theory_and<A: Prop, B: Prop>(
    f: Theory<A>,
    g: Theory<B>
) -> Theory<And<A, B>> {
    Rc::new(move |uni| match uni {
        Left(t_ab) => f(Left(tauto_rev_and(t_ab).0)),
        Right(p_ab) => match para_and_to_or(p_ab) {
            Left(p_a) => f(Right(p_a)),
            Right(p_b) => g(Right(p_b)),
        }
    })
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
    use super::*;

    fn pow_eq<A: Prop, B: Prop>()
        where Pow<A, B>: PowImply<B, A>,
              Pow<B, A>: PowImply<A, B>
    {
        let _: Pow<A, B> = pow();
        let _: Pow<B, A> = pow();
    }

    fn pow_eq_symmetry<A: Prop, B: Prop>()
        where Pow<A, B>: PowImply<B, A>,
              Pow<B, A>: PowImply<A, B>
    {
        pow_eq::<B, A>()
    }

    fn check1<A: Prop>() {pow_eq::<True, Eq<A, A>>()}
    fn check2<A: Prop, B: Prop, C: Prop>() {pow_eq::<And<Pow<A, C>, Pow<B, C>>, Pow<And<A, B>, C>>()}
    fn check3<A: Prop, B: Prop, C: Prop>() {pow_eq::<Or<Pow<A, C>, Pow<B, C>>, Pow<Or<A, B>, C>>()}
    fn check4<A: Prop, B: Prop>() {pow_eq::<Not<Pow<A, B>>, Pow<Not<A>, B>>()}
    fn check5<A: Prop, B: Prop, C: Prop>() {pow_eq::<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>>()}
    fn check6<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>>()}
    fn check7<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>>()}
    fn check8<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Eq<A, B>>, Eq<Pow<C, A>, Pow<C, B>>>()}
}
