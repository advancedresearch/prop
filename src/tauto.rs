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

impl<A: DProp> Decidable for Tauto<A> {
    fn decide() -> ExcM<Tauto<A>> {
        fn f<A: DProp>(_: True) -> ExcM<A> {A::decide()}
        let f: Or<Tauto<A>, Tauto<Not<A>>> = hooo_or()(f::<A>);
        match f {
            Left(tauto_a) => Left(tauto_a),
            Right(tauto_na) => Right(hooo_not()(tauto_na))
        }
    }
}

/// `a^b`.
pub type Pow<A, B> = fn(B) -> A;

/// Power equivalence `=^=`.
pub type PowEq<A, B> = And<Pow<B, A>, Pow<A, B>>;

/// `a^b => (a^b)^c`.
pub fn pow_lift<A: Prop, B: Prop, C: Prop>(_: Pow<A, B>) -> Pow<Pow<A, B>, C> {
    unimplemented!()
}

/// `b^a ⋀ c^b => c^a`.
pub fn pow_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Pow<B, A>,
    bc: Pow<C, B>,
) -> Pow<C, A> {
    fn f<A: Prop, B: Prop, C: Prop>(a: A) -> Imply<And<B, Imply<B, Pow<C, B>>>, C> {
        Rc::new(move |(b, bc)| {
            let bc = bc(b.clone())(b.clone());
            imply::transitivity(b.map_any(), bc.map_any())(a.clone())
        })
    }
    let f: Imply<Pow<And<B, Imply<B, Pow<C, B>>>, A>, Pow<C, A>> = hooo_imply()(f::<A, B, C>);
    let f = imply::in_left(f,
        |x: And<Pow<B, A>, Imply<Pow<B, A>, Pow<Pow<C, B>, A>>>| {
            let x: And<Pow<B, A>, Imply<Pow<B, A>, Pow<Pow<C, B>, A>>> = x;
            let x: And<Pow<B, A>, Pow<Imply<B, Pow<C, B>>, A>> = and::in_right(x,
                |x| hooo_rev_imply()(x)
            );
            hooo_rev_and()(x)
        }
    );
    let f: Imply<Imply<Pow<B, A>, Pow<Pow<C, B>, A>>, Pow<C, A>> = imply::chain(f)(ab);
    f(pow_lift(bc).map_any())
}

/// `x =^= x`.
pub fn pow_eq_refl<A: Prop>() -> PowEq<A, A> {
    fn f<A: Prop>(a: A) -> A {a}
    (f, f)
}
/// `(x =^= y) => (y =^= x)`.
pub fn pow_eq_symmetry<A: Prop, B: Prop>((ab, ba): PowEq<A, B>) -> PowEq<B, A> {(ba, ab)}
/// `(x =^= y) ⋀ (y =^= z) => (x =^= z)`.
pub fn pow_eq_transitivity<A: Prop, B: Prop, C: Prop>(
    (ab, ba): PowEq<A, B>,
    (bc, cb): PowEq<B, C>
) -> PowEq<A, C> {
    let ca: Pow<A, C> = pow_transitivity(cb, ba);
    let ac: Pow<C, A> = pow_transitivity(ab, bc);
    (ac, ca)
}

#[marker]
/// Implemented by exponential propositions.
pub trait PowImply<A, B>: Fn(A) -> B {}

impl<A, B, C> PowImply<And<Para<Eq<A, B>>, Tauto<Eq<B, C>>>, Para<Eq<A, C>>>
    for Pow<Para<Eq<A, C>>, And<Para<Eq<A, B>>, Tauto<Eq<B, C>>>> {}
impl<A, B, C> PowImply<And<Tauto<Eq<A, B>>, Para<Eq<B, C>>>, Para<Eq<A, C>>>
    for Pow<Para<Eq<A, C>>, And<Tauto<Eq<A, B>>, Para<Eq<B, C>>>> {}

impl<A, B> PowImply<Para<Eq<A, B>>, Para<Eq<B, A>>> for Pow<Para<Eq<B, A>>, Para<Eq<A, B>>> {}

impl<A, B> PowImply<Pow<Not<A>, B>, Not<Pow<A, B>>>
    for Pow<Not<Pow<A, B>>, Pow<Not<A>, B>> {}
impl<A, B> PowImply<Not<Pow<A, B>>, Pow<Not<A>, B>>
    for Pow<Pow<Not<A>, B>, Not<Pow<A, B>>> {}

macro_rules! hooo_impl {
    (dir $x:tt, $y:tt) => {
        impl<A, B, C> PowImply<Pow<$x<A, B>, C>, $x<Pow<A, C>, Pow<B, C>>>
            for Pow<$x<Pow<A, C>, Pow<B, C>>, Pow<$x<A, B>, C>> {}
        impl<A, B, C> PowImply<$x<Pow<A, C>, Pow<B, C>>, Pow<$x<A, B>, C>>
            for Pow<Pow<$x<A, B>, C>, $x<Pow<A, C>, Pow<B, C>>> {}
        impl<A, B, C> PowImply<Pow<C, $x<A, B>>, $y<Pow<C, A>, Pow<C, B>>>
            for Pow<$y<Pow<C, A>, Pow<C, B>>, Pow<C, $x<A, B>>> {}
        impl<A, B, C> PowImply<$y<Pow<C, A>, Pow<C, B>>, Pow<C, $x<A, B>>>
            for Pow<Pow<C, $x<A, B>>, $y<Pow<C, A>, Pow<C, B>>> {}
    };
    ($x:tt, $y:tt) => {
        hooo_impl!{dir $x, $y}
        hooo_impl!{dir $y, $x}
    };
}

hooo_impl!{And, Or}

type NEq<A, B> = Not<Eq<A, B>>;
hooo_impl!{Eq, NEq}

type NRImply<A, B> = Not<Imply<B, A>>;
hooo_impl!{Imply, NRImply}

/// Get instance of exponential proposition.
pub fn pow<A: Prop, B: Prop>() -> Pow<A, B>
    where Pow<A, B>: PowImply<B, A>
{unimplemented!()}

/// Get tautological proposition.
pub fn tauto<A: Prop>() -> Tauto<A>
    where Tauto<A>: PowImply<True, A>
{
    pow()
}

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

/// `(¬(c^a == c^b))^(c^(a == b))`.
pub fn hooo_dual_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Not<Eq<Pow<C, A>, Pow<C, B>>>, Pow<C, Eq<A, B>>> {pow()}

/// `(c^(a == b))^¬(c^a == c^b)`.
pub fn hooo_dual_rev_eq<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<C, Eq<A, B>>, Not<Eq<Pow<C, A>, Pow<C, B>>>> {pow()}

/// `(a^c => b^c)^((a => b)^c)`.
pub fn hooo_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>> {pow()}

/// `((a => b)^c)^(a^c => b^c)`.
pub fn hooo_rev_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<Imply<A, B>, C>, Imply<Pow<A, C>, Pow<B, C>>> {pow()}

/// `(¬(c^b => c^a))^(c^(a => b))`.
pub fn hooo_dual_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Not<Imply<Pow<C, B>, Pow<C, A>>>, Pow<C, Imply<A, B>>> {pow()}

/// `(c^(a => b))^(¬(c^b => c^a))`.
pub fn hooo_dual_rev_imply<A: Prop, B: Prop, C: Prop>()
-> Pow<Pow<C, Imply<A, B>>, Not<Imply<Pow<C, B>, Pow<C, A>>>> {pow()}

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

/// `true^a`.
pub fn tr<A: Prop>() -> Pow<True, A> {
    fn f<A: Prop>(_: A) -> True {True}
    f::<A>
}

/// `a^false`.
pub fn fa<A: Prop>() -> Pow<A, False> {
    fn f<A: Prop>(fa: False) -> A {imply::absurd()(fa)}
    f::<A>
}

/// A consistent logic can't prove `false` without further assumptions.
pub fn consistency() -> Not<Tauto<False>> {
    Rc::new(move |f| f(True))
}

/// `a^true => (a == true)^true`.
pub fn tauto_to_eq_true<A: Prop>(
    x: Tauto<A>
) -> Tauto<Eq<A, True>> {
    fn f<A: Prop>(_: True) -> Imply<A, Eq<A, True>> {
        Rc::new(move |a| (True.map_any(), a.map_any()))
    }
    let f = hooo_imply()(f);
    f(x)
}

/// `(a == true)^true => a^true`.
pub fn tauto_from_eq_true<A: Prop>(
    x: Tauto<Eq<A, True>>
) -> Tauto<A> {
    fn f<A: Prop>(_: True) -> Imply<Eq<A, True>, A> {
        Rc::new(move |eq| eq.1(True))
    }
    let f = hooo_imply()(f);
    f(x)
}

/// `false^a => (a == false)^true`.
pub fn para_to_eq_false<A: DProp>(
    x: Para<A>
) -> Tauto<Eq<A, False>> {
    let y: Not<Tauto<A>> = Rc::new(move |tauto_a| {
        x(tauto_a(True))
    });
    let eq: Eq<Not<Tauto<False>>, Not<Tauto<A>>> = (
        y.map_any(),
        consistency().map_any(),
    );
    let eq2: Eq<Tauto<A>, Tauto<False>> = eq::rev_modus_tollens(eq);
    hooo_rev_eq()(eq2)
}

/// `¬(x^true) => (¬x)^true`.
pub fn tauto_not<A: Prop>(x: Not<Tauto<A>>) -> Tauto<Not<A>> {
    hooo_rev_not()(x)
}

/// `(¬x)^true => ¬(x^true)`.
pub fn tauto_rev_not<A: Prop>(x: Tauto<Not<A>>) -> Not<Tauto<A>> {
    hooo_not()(x)
}

/// `x^true => (¬¬x)^true`.
pub fn tauto_not_double<A: Prop>(x: Tauto<A>) -> Tauto<Not<Not<A>>> {
    fn f<A: Prop>(_: True) -> Imply<A, Not<Not<A>>> {
        Rc::new(move |a| not::double(a))
    }
    let f = hooo_imply()(f);
    f(x)
}

/// `false^(¬x) => ¬false^x`.
pub fn para_rev_not<A: Prop>(x: Para<Not<A>>) -> Not<Para<A>> {
    let y: Not<Imply<Para<False>, Para<A>>> = hooo_dual_imply()(x);
    let y2: Not<Para<A>> = Rc::new(move |para_na| {
        y(para_na.map_any())
    });
    y2
}

/// `(x == x)^true`.
pub fn eq_refl<A: Prop>() -> Tauto<Eq<A, A>> {
    fn f<A: Prop>(_: True) -> Eq<A, A> {eq::refl()}
    f::<A>
}

/// `(x == y)^true => (y == x)^true`.
pub fn tauto_eq_symmetry<A: Prop, B: Prop>(x: Tauto<Eq<A, B>>) -> Tauto<Eq<B, A>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Eq<A, B>, Eq<B, A>> {
        Rc::new(move |ab| eq::symmetry(ab))
    }
    let f = hooo_imply()(f);
    f(x)
}

/// `false^(x == y) => false^(y == x)`.
pub fn para_eq_symmetry<A: Prop, B: Prop>(x: Para<Eq<A, B>>) -> Para<Eq<B, A>> {
    pow()(x)
}

/// `(a == b)^true ∧ (b == c)^true => (a == c)^true`.
pub fn tauto_eq_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Eq<A, B>>,
    bc: Tauto<Eq<B, C>>
) -> Tauto<Eq<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True) ->
    Imply<Eq<A, B>, Imply<Eq<B, C>, Eq<A, C>>> {
        Rc::new(move |ab| Rc::new(move |bc| eq::transitivity(ab.clone(), bc)))
    }
    let f = hooo_imply()(f);
    let g = hooo_imply()(f(ab));
    g(bc)
}

pub use tauto_eq_transitivity as tauto_eq_in_right_arg;

/// `(a == b) ∧ (a == c) => (c == b)`.
pub fn tauto_eq_in_left_arg<A: Prop, B: Prop, C: Prop>(
    f: Tauto<Eq<A, B>>,
    g: Tauto<Eq<A, C>>,
) -> Tauto<Eq<C, B>> {
    tauto_eq_transitivity(tauto_eq_symmetry(g), f)
}

/// `(a^true == b^true) => (false^a == false^b)`.
pub fn eq_tauto_to_eq_para<A: Prop, B: Prop>(
    _: Eq<Tauto<A>, Tauto<B>>
) -> Eq<Para<A>, Para<B>> {
    unimplemented!()
}

/// `(a^true == b^true) => (false^a == false^b)`.
pub fn eq_para_to_eq_tauto<A: Prop, B: Prop>(
    _: Eq<Para<A>, Para<B>>
) -> Eq<Tauto<A>, Tauto<B>> {
    unimplemented!()
}

/// `(false^a ∧ (a == b)^true) => false^b`.
pub fn para_in_arg<A: Prop, B: Prop>(
    para_a: Para<A>,
    tauto_eq_a_b: Tauto<Eq<A, B>>
) -> Para<B> {
    unimplemented!()
}

/// `(false^(a == b) ∧ (b == c)^true) => false^(a == c)`.
pub fn para_eq_transitivity_left<A: Prop, B: Prop, C: Prop>(
    ab: Para<Eq<A, B>>,
    bc: Tauto<Eq<B, C>>
) -> Para<Eq<A, C>> {
    pow()((ab, bc))
}

/// `((a == b)^true ∧ false^(b == c)) => false^(a == c)`.
pub fn para_eq_transitivity_right<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Eq<A, B>>,
    bc: Para<Eq<B, C>>
) -> Para<Eq<A, C>> {
    pow()((ab, bc))
}

/// `x => x`.
pub fn imply_refl<A: Prop>() -> Imply<A, A> {
    Rc::new(move |x| x)
}

/// `(a => b)^true ∧ (b => c)^true => (a => c)^true`.
pub fn tauto_imply_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    bc: Tauto<Imply<B, C>>,
) -> Tauto<Imply<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True) -> Imply<And<Imply<A, B>, Imply<B, C>>, Imply<A, C>> {
        Rc::new(move |(ab, bc)| imply::transitivity(ab, bc))
    }
    let f = hooo_imply()(f::<A, B, C>);
    let x = hooo_rev_and()((ab, bc));
    f(x)
}

/// `(a^true ∧ b^true) => (a == b)^true`.
pub fn tauto_and_to_eq_pos<A: Prop, B: Prop>(a: Tauto<A>, b: Tauto<B>) -> Tauto<Eq<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<And<A, B>, Eq<A, B>> {
        Rc::new(move |ab| and::to_eq_pos(ab))
    }
    let f = hooo_imply()(f::<A, B>);
    let x = hooo_rev_and()((a, b));
    f(x)
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

    fn check2<A: Prop, B: Prop, C: Prop>() {pow_eq::<And<Pow<A, C>, Pow<B, C>>, Pow<And<A, B>, C>>()}
    fn check3<A: Prop, B: Prop, C: Prop>() {pow_eq::<Or<Pow<A, C>, Pow<B, C>>, Pow<Or<A, B>, C>>()}
    fn check4<A: Prop, B: Prop>() {pow_eq::<Not<Pow<A, B>>, Pow<Not<A>, B>>()}
    fn check5<A: Prop, B: Prop, C: Prop>() {pow_eq::<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>>()}
    fn check6<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>>()}
    fn check7<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>>()}
    fn check8<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Eq<A, B>>, Not<Eq<Pow<C, A>, Pow<C, B>>>>()}
    fn check9<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Imply<A, B>>, Not<Imply<Pow<C, B>, Pow<C, A>>>>()}
}
