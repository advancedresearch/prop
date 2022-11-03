//! # Exponential Propositions
//!
//! By using function pointers,
//! one can force construction of propositions
//! without capturing any variables,
//! such that the proposition is tautological true,
//! instead of just assuming it is true.
//!
//! When `a` is tautological provable from `b`,
//! one expresses it as `a^b`.
//!
//! It turns out that this has the same semantics
//! as [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading) (HOOO).
//!
//! One motivation for developing HOOO for Exponential Propositions
//! is to allow substitution in quality `~~` and qubit `~` operator
//! for Path Semantical Quantum Propositional Logic (PSQ).
//!
//! ### Comment conventions
//!
//! When a function comment says `a => b`, it is actually `(a => b)^true`.
//!
//! The exponent is left out to make the comments more consistent for the whole library.
//! Otherwise, it would be proper to use notation for Exponential Propositions everywhere,
//! but this is unpractical since Exponential Propositions is viewed as an extension of
//! normal Propositional Logic. One would like other modules to not use this notation
//! unless they rely on this extension explicitly.
//!
//! When `a^true` is used explicitly, the function returns a function pointer instead of using a
//! `_: True` argument, since it is natural in programming to not add unused arguments.

use crate::*;
use quality::Q;
use qubit::Qu;

impl<A: DProp, B: DProp> Decidable for Pow<A, B> {
    fn decide() -> ExcM<Self> {decide()}
}

/// `a^b ⋁ ¬(a^b)`.
pub fn decide<A: DProp, B: DProp>() -> ExcM<Pow<A, B>> {
    fn f<A: DProp, B: Prop>(_: B) -> ExcM<A> {A::decide()}
    match hooo_or(f) {
        Left(pow_ab) => Left(pow_ab),
        Right(pow_na_b) => {
            match para_decide::<B>() {
                Left(para_b) => Left(pow_transitivity(para_b, fa())),
                Right(npara_b) => {
                    match para_decide::<A>() {
                        Left(para_a) => {
                            Right(Rc::new(move |pow_ab| {
                                let para_b = pow_transitivity(pow_ab, para_a);
                                let nb: Not<B> = Rc::new(move |b| para_b(b));
                                let para_nb = pow_not(npara_b.clone());
                                para_nb(nb)
                            }))
                        }
                        Right(npara_a) => {
                            let para_na = pow_not(npara_a);
                            let para_b = pow_transitivity(pow_na_b, para_na);
                            let nb: Not<B> = Rc::new(move |b| para_b(b));
                            let para_nb = pow_not(npara_b);
                            imply::absurd()(para_nb(nb))
                        }
                    }

                }
            }
        }
    }
}

/// `a^true ⋁ ¬(a^true)`.
pub fn tauto_decide<A: DProp>() -> ExcM<Tauto<A>> {
    decide()
}

/// `false^a ⋁ ¬(false^a)`.
pub fn para_decide<A: Prop>() -> ExcM<Para<A>> {
    fn f<A: Prop>((a, na): And<A, Not<A>>) -> False {na(a)}
    let f = hooo_dual_and(f);
    match f {
        Left(para_a) => Left(para_a),
        Right(para_na) => Right(pow_rev_not(para_na)),
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

/// `(a^b)^c => a^(b ⋀ c)`.
pub fn pow_lower<A: Prop, B: Prop, C: Prop>(x: Pow<Pow<A, B>, C>) -> Pow<A, And<B, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(pow_ab: Pow<A, B>) -> Pow<A, And<B, C>> {
        fn g<A: Prop, B: Prop>((a, _): And<A, B>) -> A {a}
        pow_transitivity(g, pow_ab)
    }
    fn g<A: Prop, B: Prop, C: Prop>(_: C) -> Imply<Pow<A, B>, Pow<A, And<B, C>>> {
        Rc::new(move |pow_ab| f(pow_ab))
    }
    fn h<A: Prop, B: Prop, C: Prop>(x: Pow<Pow<A, And<B, C>>, C>) -> Pow<A, And<B, C>> {
        fn f2<A: Prop, B: Prop, C: Prop>((b, c): And<B, C>) -> Imply<Pow<Pow<A, And<B, C>>, C>, A> {
            Rc::new(move |x| x(c.clone())((b.clone(), c.clone())))
        }
        hooo_imply(f2)(pow_lift(x))
    }
    h(hooo_imply(g)(x))
}

/// `a => a`.
pub fn pow_refl<A: Prop>(x: A) -> A {x}

/// `a^b ⋀ (a == c)^true => c^b`.
pub fn pow_in_left_arg<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, B>,
    tauto_eq_a_c: Tauto<Eq<A, C>>,
) -> Pow<C, B> {
    fn f<A: Prop, C: Prop>((a, x): And<A, Tauto<Eq<A, C>>>) -> C {
        x(True).0(a)
    }
    pow_transitivity(hooo_rev_and((x, pow_lift(tauto_eq_a_c))), f)
}

/// `a^b ⋀ (b == c)^true => a^c`.
pub fn pow_in_right_arg<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, B>,
    tauto_eq_b_c: Tauto<Eq<B, C>>,
) -> Pow<A, C> {
    fn f<B: Prop, C: Prop>(c: C) -> Imply<Tauto<Eq<B, C>>, B> {
        Rc::new(move |x| x(True).1(c.clone()))
    }
    let y: Pow<Tauto<Eq<B, C>>, C> = pow_lift(tauto_eq_b_c);
    let pow_bc: Pow<B, C> = hooo_imply(f)(y);
    pow_transitivity(pow_bc, x)
}

/// `a^(b ⋀ c) => a^(c ⋀ b)`
pub fn pow_right_and_symmetry<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, And<B, C>>
) -> Pow<A, And<C, B>> {
    fn f<A: Prop, B: Prop>((a, b): And<A, B>) -> And<B, A> {(b, a)}
    pow_transitivity(f, x)
}

/// `¬a^b => a^(¬b)`.
pub fn pow_not<A: Prop, B: Prop>(x: Not<Pow<A, B>>) -> Pow<A, Not<B>> {
    hooo_dual_rev_imply(Rc::new(move |y: Imply<Pow<A, False>, Pow<A, B>>|
        imply::absurd()(x(y(fa())))))
}

/// `a^(¬b) => ¬a^b`.
pub fn pow_rev_not<A: Prop, B: Prop>(x: Pow<A, Not<B>>) -> Not<Pow<A, B>> {
    let y = hooo_dual_imply(x);
    Rc::new(move |pow_a_b| {
        y(pow_a_b.map_any())
    })
}

/// `a^(¬¬b) => (¬¬a)^b`.
pub fn pow_not_double_down<A: Prop, B: Prop>(x: Pow<A, Not<Not<B>>>) -> Pow<Not<Not<A>>, B> {
    hooo_rev_not(pow_rev_not(hooo_rev_not(pow_rev_not(x))))
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
    let f: Imply<Pow<And<B, Imply<B, Pow<C, B>>>, A>, Pow<C, A>> = hooo_imply(f::<A, B, C>);
    let f = imply::in_left(f,
        |x: And<Pow<B, A>, Imply<Pow<B, A>, Pow<Pow<C, B>, A>>>| {
            let x: And<Pow<B, A>, Imply<Pow<B, A>, Pow<Pow<C, B>, A>>> = x;
            let x: And<Pow<B, A>, Pow<Imply<B, Pow<C, B>>, A>> = and::in_right(x,
                |x| hooo_rev_imply(x)
            );
            hooo_rev_and(x)
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

/// `(x =^= y) => (a == b)^true`.
pub fn pow_eq_to_tauto_eq<A: Prop, B: Prop>((ba, ab): PowEq<A, B>) -> Tauto<Eq<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Pow<A, B>, Imply<B, A>> {
        Rc::new(move |ba| Rc::new(move |b| ba(b)))
    }
    let f1 = hooo_imply(f);
    let tauto_ba = f1(pow_lift(ab));
    let f2 = hooo_imply(f);
    let tauto_ab = f2(pow_lift(ba));
    hooo_rev_and((tauto_ab, tauto_ba))
}

/// `(a == b)^true => (x =^= y)`.
pub fn tauto_eq_to_pow_eq<A: Prop, B: Prop>(x: Tauto<Eq<A, B>>) -> PowEq<A, B> {
    let pow_ab: Pow<A, B> = pow_in_right_arg(pow_refl, x.clone());
    let pow_ba: Pow<B, A> = pow_in_left_arg(pow_refl, x);
    (pow_ba, pow_ab)
}

#[marker]
/// Implemented by axiomatic exponential propositions.
///
/// This is used by `pow` to instantiate an exponential proposition axiomatically.
pub trait PowImply<A, B>: Fn(A) -> B {}

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

/// `¬(a^b) => (¬a)^b`.
pub fn hooo_rev_not<A: Prop, B: Prop>(x: Not<Pow<A, B>>) -> Pow<Not<A>, B> {
    fn f<A: Prop, B: Prop>(_: True) -> Eq<Pow<A, Not<B>>, Not<Pow<A, B>>> {
        (Rc::new(move |x| pow_rev_not(x)), Rc::new(move |x| pow_not(x)))
    }
    let y: Imply<Pow<A, B>, Pow<Pow<A, B>, B>> = Rc::new(move |x| pow_lift(x));
    let x = hooo_imply(pow_in_left_arg(pow_lift(pow_not(x)), f));
    hooo_rev_imply(imply::transitivity(y, x))
}

/// `(a ⋀ b)^c => (a^c ⋀ b^c)`.
pub fn hooo_and<A: Prop, B: Prop, C: Prop>(x: Pow<And<A, B>, C>) -> And<Pow<A, C>, Pow<B, C>> {
    pow()(x)
}

/// `(a^c ⋀ b^c) => (a ⋀ b)^c`.
pub fn hooo_rev_and<A: Prop, B: Prop, C: Prop>(
    x: And<Pow<A, C>, Pow<B, C>>
) -> Pow<And<A, B>, C> {pow()(x)}

/// `c^(a ⋀ b) => (c^a ⋁ c^b)`.
pub fn hooo_dual_and<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, And<A, B>>
) -> Or<Pow<C, A>, Pow<C, B>> {pow()(x)}

/// `(c^a ⋁ c^b) => c^(a ⋀ b)`.
pub fn hooo_dual_rev_and<A: Prop, B: Prop, C: Prop>(
    x: Or<Pow<C, A>, Pow<C, B>>
) -> Pow<C, And<A, B>> {pow()(x)}

/// `(a ⋁ b)^c => (a^c ⋁ b^c)`.
pub fn hooo_or<A: Prop, B: Prop, C: Prop>(
    x: Pow<Or<A, B>, C>
) -> Or<Pow<A, C>, Pow<B, C>> {pow()(x)}

/// `(a^c ⋁ b^c) => (a ⋁ b)^c`.
pub fn hooo_rev_or<A: Prop, B: Prop, C: Prop>(
    x: Or<Pow<A, C>, Pow<B, C>>
) -> Pow<Or<A, B>, C> {pow()(x)}

/// `c^(a ⋁ b) => (c^a ⋀ c^b)`.
pub fn hooo_dual_or<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, Or<A, B>>
) -> And<Pow<C, A>, Pow<C, B>> {pow()(x)}

/// `(c^a ⋀ c^b) => c^(a ⋁ b)`.
pub fn hooo_dual_rev_or<A: Prop, B: Prop, C: Prop>(
    x: And<Pow<C, A>, Pow<C, B>>
) -> Pow<C, Or<A, B>> {pow()(x)}

/// `(a == b)^c => (a^c == b^c)`.
pub fn hooo_eq<A: Prop, B: Prop, C: Prop>(x: Pow<Eq<A, B>, C>) -> Eq<Pow<A, C>, Pow<B, C>> {
    pow()(x)
}

/// `(a^c == b^c) => (a == b)^c`.
pub fn hooo_rev_eq<A: Prop, B: Prop, C: Prop>(x: Eq<Pow<A, C>, Pow<B, C>>) -> Pow<Eq<A, B>, C> {
    pow()(x)
}

/// `c^(a == b) => ¬(c^a == c^b)`.
pub fn hooo_dual_eq<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, Eq<A, B>>
) -> Not<Eq<Pow<C, A>, Pow<C, B>>> {pow()(x)}

/// `¬(c^a == c^b) => c^(a == b)`.
pub fn hooo_dual_rev_eq<A: Prop, B: Prop, C: Prop>(
    x: Not<Eq<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, Eq<A, B>> {pow()(x)}

/// `(¬(a == b))^c => ¬(a^c == b^c)`.
pub fn hooo_neq<A: Prop, B: Prop, C: Prop>(x: Pow<NEq<A, B>, C>) -> NEq<Pow<A, C>, Pow<B, C>> {
    pow()(x)
}

/// `¬(a^c == b^c) => (¬(a == b))^c`.
pub fn hooo_rev_neq<A: Prop, B: Prop, C: Prop>(x: NEq<Pow<A, C>, Pow<B, C>>) -> Pow<NEq<A, B>, C> {
    pow()(x)
}

/// `c^(¬(a == b)) => (c^a == c^b)`.
pub fn hooo_dual_neq<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, NEq<A, B>>
) -> Eq<Pow<C, A>, Pow<C, B>> {pow()(x)}

/// `(c^a == c^b) => c^(¬(a == b))`.
pub fn hooo_dual_rev_neq<A: Prop, B: Prop, C: Prop>(
    x: Eq<Pow<C, A>, Pow<C, B>>
) -> Pow<C, NEq<A, B>> {pow()(x)}

/// `(a => b)^c => (a^c => b^c)`.
pub fn hooo_imply<A: Prop, B: Prop, C: Prop>(
    x: Pow<Imply<A, B>, C>
) -> Imply<Pow<A, C>, Pow<B, C>> {pow()(x)}

/// `(a^c => b^c) => (a => b)^c`.
pub fn hooo_rev_imply<A: Prop, B: Prop, C: Prop>(
    x: Imply<Pow<A, C>, Pow<B, C>>
) -> Pow<Imply<A, B>, C> {pow()(x)}

/// `c^(a => b) => ¬(c^b => c^a)`.
pub fn hooo_dual_imply<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, Imply<A, B>>
) -> Not<Imply<Pow<C, B>, Pow<C, A>>> {pow()(x)}

/// `¬(c^b => c^a) => c^(a => b)`.
pub fn hooo_dual_rev_imply<A: Prop, B: Prop, C: Prop>(
    x: Not<Imply<Pow<C, B>, Pow<C, A>>>
) -> Pow<C, Imply<A, B>> {pow()(x)}

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
    fn f<A: Prop>(x: False) -> A {imply::absurd()(x)}
    f::<A>
}

/// A consistent logic can't prove `false` without further assumptions.
pub fn consistency() -> Not<Tauto<False>> {
    Rc::new(move |f| f(True))
}

/// `a^true ∧ (a == b)^true => b^true`.
pub fn tauto_in_arg<A: Prop, B: Prop>(
    a: Tauto<A>,
    eq: Tauto<Eq<A, B>>
) -> Tauto<B> {
    hooo_eq(eq).0(a)
}

/// `a^true => (a == true)^true`.
pub fn tauto_to_eq_true<A: Prop>(
    x: Tauto<A>
) -> Tauto<Eq<A, True>> {
    fn f<A: Prop>(_: True) -> Imply<A, Eq<A, True>> {
        Rc::new(move |a| (True.map_any(), a.map_any()))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `(a == true)^true => a^true`.
pub fn tauto_from_eq_true<A: Prop>(
    x: Tauto<Eq<A, True>>
) -> Tauto<A> {
    fn f<A: Prop>(_: True) -> Imply<Eq<A, True>, A> {
        Rc::new(move |eq| eq.1(True))
    }
    let f = hooo_imply(f);
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
    let eq2: Eq<Tauto<A>, Tauto<False>> = eq::rev_modus_tollens_excm(
        eq, tauto_decide(), tauto_decide());
    hooo_rev_eq(eq2)
}

/// `¬(x^true) => (¬x)^true`.
pub fn tauto_not<A: Prop>(x: Not<Tauto<A>>) -> Tauto<Not<A>> {
    hooo_rev_not(x)
}

/// `(¬x)^true => ¬(x^true)`.
pub fn tauto_rev_not<A: Prop>(x: Tauto<Not<A>>) -> Not<Tauto<A>> {
    Rc::new(move |tauto_a| x(True)(tauto_a(True)))
}

/// `(¬a)^true => false^a`.
pub fn tauto_not_to_para<A: Prop>(x: Tauto<Not<A>>) -> Para<A> {
    fn f<A: Prop>(a: A) -> Imply<Tauto<Not<A>>, False> {
        Rc::new(move |x| x(True)(a.clone()))
    }
    hooo_imply(f)(pow_lift(x))
}

/// `false^a => (¬a)^true`.
pub fn para_to_tauto_not<A: Prop>(x: Para<A>) -> Tauto<Not<A>> {
    fn f<A: Prop>(_: True) -> Imply<Para<A>, Not<A>> {
        Rc::new(move |x| Rc::new(move |a| x(a)))
    }
    let x: Tauto<Para<A>> = pow_lift(x);
    hooo_imply(f)(x)
}

/// `x^true => (¬¬x)^true`.
pub fn tauto_not_double<A: Prop>(x: Tauto<A>) -> Tauto<Not<Not<A>>> {
    fn f<A: Prop>(_: True) -> Imply<A, Not<Not<A>>> {
        Rc::new(move |a| not::double(a))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `false^(¬x) => ¬false^x`.
pub fn para_rev_not<A: Prop>(x: Para<Not<A>>) -> Not<Para<A>> {
    pow_rev_not(x)
}

/// `false^a => false^(¬¬a)`.
pub fn para_not_double<A: Prop>(x: Para<A>) -> Para<Not<Not<A>>> {
    match para_decide::<Not<Not<A>>>() {
        Left(y) => y,
        Right(y) => {
            let y: Not<Not<Para<Not<A>>>> = imply::in_left(y, |x| pow_not(x));
            let y: Not<Not<Not<Para<A>>>> = imply::in_left(y, |x| imply::in_left(x, |y| pow_rev_not(y)));
            not::absurd(not::rev_triple(y), x)
        }
    }
}

/// `false^(¬¬a) => false^a`.
pub fn para_not_rev_double<A: Prop>(x: Para<Not<Not<A>>>) -> Para<A> {
    fn f<A: Prop>(a: A) -> Not<Not<A>> {not::double(a)}
    pow_transitivity(f, x)
}

/// `false^(¬x) => false^(¬¬¬x)`.
pub fn para_not_triple<A: Prop>(x: Para<Not<A>>) -> Para<Not<Not<Not<A>>>> {
    fn f<A: Prop>(_: True) -> Eq<Not<A>, Not<Not<Not<A>>>> {
        (Rc::new(move |x| not::double(x)), Rc::new(move |x| not::rev_triple(x)))
    }
    para_in_arg(x, f)
}

/// `false^(¬¬¬x) => false^(¬x)`.
pub fn para_not_rev_triple<A: Prop>(x: Para<Not<Not<Not<A>>>>) -> Para<Not<A>> {
    fn f<A: Prop>(_: True) -> Eq<Not<A>, Not<Not<Not<A>>>> {
        (Rc::new(move |x| not::double(x)), Rc::new(move |x| not::rev_triple(x)))
    }
    para_in_arg(x, tauto_eq_symmetry(f))
}

/// `(¬(false^a) == ¬(false^b)) => (false^a == false^b)`.
pub fn eq_not_para_to_eq_para<A: Prop, B: Prop>(
    eq_npara_a_npara_b: Eq<Not<Para<A>>, Not<Para<B>>>
) -> Eq<Para<A>, Para<B>> {
    eq::symmetry(eq::rev_modus_tollens_excm(eq_npara_a_npara_b, para_decide(), para_decide()))
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
    let f = hooo_imply(f);
    f(x)
}

/// `false^(x == y) => false^(y == x)`.
pub fn para_eq_symmetry<A: Prop, B: Prop>(x: Para<Eq<A, B>>) -> Para<Eq<B, A>> {
    pow_transitivity(eq::symmetry, x)
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
    let f = hooo_imply(f);
    let g = hooo_imply(f(ab));
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

/// `uniform(a) ⋁ false^uniform(a)`.
pub fn program<A: Prop>() -> Or<Uniform<A>, Para<Uniform<A>>> {
    match para_decide::<A>() {
        Left(para_a) => Left(Right(para_a)),
        Right(npara_a) => {
            match para_decide::<Tauto<A>>() {
                Left(para_tauto_a) => {
                    fn f<A: Prop>(para_a: Para<A>) -> Not<A> {Rc::new(move |a| para_a(a))}
                    let x = pow_transitivity(f, pow_not(npara_a));
                    Right(hooo_dual_rev_or((para_tauto_a, x)))
                }
                Right(npara_tauto_a) => {
                    fn f<A: Prop>(ntr: Not<True>) -> A {imply::absurd()(ntr(True))}
                    fn g<A: Prop>(_: True) -> Eq<Not<Tauto<A>>, Pow<A, Not<True>>> {
                        (Rc::new(move |ntauto_a| pow_not(ntauto_a)),
                         Rc::new(move |pow_a_ntr| pow_rev_not(pow_a_ntr)))
                    }
                    let x = pow_in_right_arg(pow_not(npara_tauto_a), g);
                    imply::absurd()(x(f))
                }
            }
        }
    }
}

/// `(a^true => b^true) => (false^b => false^a)`.
pub fn imply_tauto_to_imply_para<A: Prop, B: Prop>(
    x: Imply<Tauto<A>, Tauto<B>>
) -> Imply<Para<B>, Para<A>> {
    Rc::new(move |para_b| {
        match para_decide::<A>() {
            Left(para_a) => para_a,
            Right(npara_a) => {
                let nb: Not<B> = Rc::new(move |b| para_b(b));
                let na: Not<A> = imply::modus_tollens(hooo_rev_imply(x.clone())(True))(nb);
                imply::absurd()(pow_not(npara_a)(na))
            }
        }
    })
}

/// `(a^true == b^true) => (false^a == false^b)`.
pub fn eq_tauto_to_eq_para<A: Prop, B: Prop>(
    x: Eq<Tauto<A>, Tauto<B>>
) -> Eq<Para<A>, Para<B>> {
    let y0 = imply_tauto_to_imply_para(x.0);
    let y1 = imply_tauto_to_imply_para(x.1);
    (y1, y0)
}

/// `(a^true == false^a) => false^uniform(a)`.
pub fn eq_tauto_para_to_para_uniform<A: Prop>(eq: Eq<Tauto<A>, Para<A>>) -> Para<Uniform<A>> {
    match program::<A>() {
        Left(Left(tauto_a)) => imply::absurd()(eq.0(tauto_a)(tauto_a(True))),
        Left(Right(para_a)) => imply::absurd()(para_a(eq.1(para_a)(True))),
        Right(para_uni) => para_uni,
    }
}

/// `false^uniform(a) => (a^true == false^a)`.
pub fn para_uniform_to_eq_tauto_para<A: Prop>(
    para_uni: Para<Uniform<A>>
) -> Eq<Tauto<A>, Para<A>> {
    (
        Rc::new(move |tauto_a| imply::absurd()(para_uni(Left(tauto_a)))),
        Rc::new(move |para_a| imply::absurd()(para_uni(Right(para_a)))),
    )
}

/// `(false^a ∧ (a == b)^true) => false^b`.
pub fn para_in_arg<A: Prop, B: Prop>(
    para_a: Para<A>,
    tauto_eq_a_b: Tauto<Eq<A, B>>
) -> Para<B> {
    let eq = hooo_eq(tauto_eq_a_b);
    let eq2 = eq_tauto_to_eq_para(eq);
    eq2.0(para_a)
}

/// `(false^(a == b) ∧ (b == c)^true) => false^(a == c)`.
pub fn para_eq_transitivity_left<A: Prop, B: Prop, C: Prop>(
    ab: Para<Eq<A, B>>,
    bc: Tauto<Eq<B, C>>
) -> Para<Eq<A, C>> {
    let eq_para_b_para_c = eq_tauto_to_eq_para(hooo_eq(bc));
    let y = hooo_dual_eq(ab);
    let y = imply::in_left(y, move |x: Eq<Para<A>, Para<C>>| {
        eq::transitivity(x, eq::symmetry(eq_para_b_para_c.clone()))
    });
    hooo_dual_rev_eq(y)
}

/// `((a == b)^true ∧ false^(b == c)) => false^(a == c)`.
pub fn para_eq_transitivity_right<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Eq<A, B>>,
    bc: Para<Eq<B, C>>
) -> Para<Eq<A, C>> {
    let eq_para_a_para_b = eq_tauto_to_eq_para(hooo_eq(ab));
    let y = hooo_dual_eq(bc);
    let y = imply::in_left(y, move |x: Eq<Para<A>, Para<C>>| {
        eq::transitivity(eq::symmetry(eq_para_a_para_b.clone()), x)
    });
    hooo_dual_rev_eq(y)
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
    let f = hooo_imply(f::<A, B, C>);
    let x = hooo_rev_and((ab, bc));
    f(x)
}

/// `(a^true ∧ b^true) => (a == b)^true`.
pub fn tauto_and_to_eq_pos<A: Prop, B: Prop>(a: Tauto<A>, b: Tauto<B>) -> Tauto<Eq<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<And<A, B>, Eq<A, B>> {
        Rc::new(move |ab| and::to_eq_pos(ab))
    }
    let f = hooo_imply(f::<A, B>);
    let x = hooo_rev_and((a, b));
    f(x)
}

/// `a^true => (a ⋁ b)^true`.
pub fn tauto_or_left<A: Prop, B: Prop>(
    x: Tauto<A>
) -> Tauto<Or<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<A, Or<A, B>> {
        Rc::new(move |a| Left(a))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `b^true => (a ⋁ b)^true`.
pub fn tauto_or_right<A: Prop, B: Prop>(
    x: Tauto<B>
) -> Tauto<Or<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<B, Or<A, B>> {
        Rc::new(move |b| Right(b))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `(a^true ⋁ b^true) => (a ⋁ b)^true`.
pub fn tauto_or<A: Prop, B: Prop>(or_ab: Or<Tauto<A>, Tauto<B>>) -> Tauto<Or<A, B>> {
    match or_ab {
        Left(tauto_a) => tauto_or_left(tauto_a),
        Right(tauto_b) => tauto_or_right(tauto_b),
    }
}

/// `(a ⋁ b)^true => (a^true ⋁ b^true)`.
pub fn tauto_rev_or<A: Prop, B: Prop>(x: Tauto<Or<A, B>>) -> Or<Tauto<A>, Tauto<B>> {
    hooo_or(x)
}

/// `(false^a ∧ false^b) => false^(a ⋁ b)`.
pub fn para_to_or<A: Prop, B: Prop>(
    para_a: Para<A>,
    para_b: Para<B>
) -> Para<Or<A, B>> {
    hooo_dual_rev_or((para_a, para_b))
}

/// `false^(a ⋁ b) => false^a ∧ false^b`.
pub fn para_from_or<A: Prop, B: Prop>(
    x: Para<Or<A, B>>,
) -> And<Para<A>, Para<B>> {
    hooo_dual_or(x)
}

/// `false^(a ∧ b) => false^a ⋁ false^b`.
pub fn para_and_to_or<A: Prop, B: Prop>(
    x: Para<And<A, B>>
) -> Or<Para<A>, Para<B>> {
    hooo_dual_and(x)
}

/// `a^true ∧ b^true => (a ∧ b)^true`.
pub fn tauto_and<A: Prop, B: Prop>(
    tauto_a: Tauto<A>,
    tauto_b: Tauto<B>,
) -> Tauto<And<A, B>> {
    hooo_rev_and((tauto_a, tauto_b))
}

/// `(a ∧ b)^true => a^true ∧ b^true`.
pub fn tauto_rev_and<A: Prop, B: Prop>(
    tauto_and_a_b: Tauto<And<A, B>>,
) -> And<Tauto<A>, Tauto<B>> {
    hooo_and(tauto_and_a_b)
}

/// `false^a => false^(a ∧ b)`.
pub fn para_left_and<A: Prop, B: Prop>(
    para_a: Para<A>,
) -> Para<And<A, B>> {
    pow_lower(pow_lift(para_a))
}

/// `false^b => false^(a ∧ b)`.
pub fn para_right_and<A: Prop, B: Prop>(
    para_b: Para<B>,
) -> Para<And<A, B>> {
    pow_right_and_symmetry(pow_lower(pow_lift(para_b)))
}

/// `(a => b)^true ∧ (a == c)^true  =>  (c => b)^true`.
pub fn tauto_imply_in_left_arg<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    eq_a_c: Tauto<Eq<A, C>>
) -> Tauto<Imply<C, B>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True)
    -> Imply<And<Imply<A, B>, Eq<A, C>>, Imply<C, B>> {
        Rc::new(move |(ab, eq_a_c)| imply::in_left_arg(ab, eq_a_c))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, eq_a_c));
    f(x)
}

/// `(a => b)^true ∧ (b == c)^true  =>  (a => c)^true`.
pub fn tauto_imply_in_right_arg<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    eq_b_c: Tauto<Eq<B, C>>
) -> Tauto<Imply<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True)
    -> Imply<And<Imply<A, B>, Eq<B, C>>, Imply<A, C>> {
        Rc::new(move |(ab, eq_b_c)| imply::in_right_arg(ab, eq_b_c))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, eq_b_c));
    f(x)
}

/// `(a => b)^true ∧ a^true  =>  b^true`.
pub fn tauto_modus_ponens<A: Prop, B: Prop>(
    ab: Tauto<Imply<A, B>>,
    a: Tauto<A>,
) -> Tauto<B> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<And<Imply<A, B>, A>, B> {
        Rc::new(move |(ab, a)| ab(a))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, a));
    f(x)
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
        (Right(p_ab), Right(p_bc)) => Left(tauto_from_para_transitivity(p_ab, p_bc)),
    }
}

/// `(false^(a == b) ∧ false^(b == c)) => (a == c)^true`.
pub fn tauto_from_para_transitivity<A: Prop, B: Prop, C: Prop>(
    _: Para<Eq<A, B>>,
    _: Para<Eq<B, C>>,
) -> Tauto<Eq<A, C>> {
    unimplemented!()
}

/// `uniform(a) ⋀ (a == b)^true => uniform(b)`.
pub fn uniform_in_arg<A: Prop, B: Prop>(
    uni: Uniform<A>,
    eq: Tauto<Eq<A, B>>
) -> Uniform<B> {
    match uni {
        Left(tauto_a) => Left(hooo_eq(eq).0(tauto_a)),
        Right(para_a) => Right(para_in_arg(para_a, eq))
    }
}

/// `uniform(a) ∧ uniform(b) => uniform(a ∧ b)`.
pub fn uniform_and<A: Prop, B: Prop>(
    uni_a: Uniform<A>,
    uni_b: Uniform<B>
) -> Uniform<And<A, B>> {
    match (uni_a, uni_b) {
        (Left(tauto_a), Left(tauto_b)) => Left(hooo_rev_and((tauto_a, tauto_b))),
        (_, Right(para_b)) => Right(hooo_dual_rev_and(Right(para_b))),
        (Right(para_a), _) => Right(hooo_dual_rev_and(Left(para_a))),
    }
}

/// `false^uniform(a ∧ b) => false^(uniform(a) ∧ uniform(b))`.
pub fn para_uniform_and<A: Prop, B: Prop>(
    x: Para<Uniform<And<A, B>>>
) -> Para<And<Uniform<A>, Uniform<B>>> {
    fn f<A: Prop, B: Prop>((a, b): And<Uniform<A>, Uniform<B>>) -> Uniform<And<A, B>> {
        uniform_and(a, b)
    }
    pow_transitivity(f::<A, B>, x)
}

/// `uniform(a ∧ b) => uniform(a) ⋁ uniform(b)`.
pub fn uniform_dual_and<A: Prop, B: Prop>(
    uni_and: Uniform<And<A, B>>,
) -> Or<Uniform<A>, Uniform<B>> {
    match uni_and {
        Left(x) => Left(Left(hooo_and(x).0)),
        Right(para_and) => match hooo_dual_and(para_and) {
            Left(para_a) => Left(Right(para_a)),
            Right(para_b) => Right(Right(para_b)),
        }
    }
}

/// `uniform(a) ∧ uniform(b) => uniform(a ⋁ b)`.
pub fn uniform_dual_rev_or<A: Prop, B: Prop>(
    a: Uniform<A>,
    b: Uniform<B>,
) -> Uniform<Or<A, B>> {
    match (a, b) {
        (Left(tauto_a), _) => Left(tauto_or_left(tauto_a)),
        (_, Left(tauto_b)) => Left(tauto_or_right(tauto_b)),
        (Right(para_a), Right(para_b)) => Right(para_to_or(para_a, para_b)),
    }
}

/// `uniform(a) => (a ⋁ ¬a)^true`.
pub fn uniform_to_excm<A: Prop>(
    uni: Uniform<A>
) -> Tauto<ExcM<A>> {
    fn f<A: Prop>(para_a: Para<A>) -> Tauto<Not<A>> {
        hooo_rev_not(Rc::new(move |tauto_a: Tauto<A>| {
            para_a(tauto_a(True))
        }))
    }
    match uni {
        Left(t) => tauto_or_left(t),
        Right(p) => tauto_or_right(f(p)),
    }
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

/// `(false^a)^(a^true) ⋀ (a^true)^(false^a) => false`.
///
/// This is also known as [Liar's paradox](https://en.wikipedia.org/wiki/Liar_paradox).
pub fn para_liar<A: Prop>(
    f: And<Pow<Para<A>, Tauto<A>>, Pow<Tauto<A>, Para<A>>>
) -> False {
    let f = pow_eq_to_tauto_eq(f);
    match para_decide::<A>() {
        Left(para_a) => para_a(f(True).1(para_a)(True)),
        Right(npara_a) => {
            let ntauto_a = eq::modus_tollens(f(True)).0(npara_a.clone());
            let tauto_na = hooo_rev_not(ntauto_a);
            let para_a = tauto_not_to_para(tauto_na);
            npara_a(para_a)
        }
    }
}

/// `(a => b)^true => b^a`.
pub fn tauto_imply_to_pow<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<B, A> {
    fn f<A: Prop, B: Prop>(a: A) -> Imply<Tauto<Imply<A, B>>, B> {
        Rc::new(move |x| x(True)(a.clone()))
    }
    hooo_imply(f)(pow_lift(x))
}

/// `b^a => (a => b)^true`.
pub fn pow_to_tauto_imply<A: Prop, B: Prop>(
    x: Pow<B, A>
) -> Tauto<Imply<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Pow<B, A>, Imply<A, B>> {
        Rc::new(|pow_ba| Rc::new(move |a| pow_ba(a)))
    }
    let f: Imply<Pow<Pow<B, A>, True>, Tauto<Imply<A, B>>> = hooo_imply(f);
    f(pow_lift(x))
}

/// `(a => b)^true => (b^a)^true`.
pub fn tauto_pow_imply<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<Pow<B, A>, True> {
    pow_lift(tauto_imply_to_pow(x))
}

/// `(b^a)^true => (a => b)^true`.
pub fn tauto_imply_pow<A: Prop, B: Prop>(
    x: Pow<Pow<B, A>, True>
) -> Tauto<Imply<A, B>> {
    pow_to_tauto_imply(x(True))
}

/// `(a => b)^true => b^(a^true)`.
pub fn tauto_imply_to_pow_tauto<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<B, Tauto<A>> {
    fn f<A: Prop>(tauto_a: Tauto<A>) -> A {tauto_a(True)}
    pow_transitivity(f, tauto_imply_to_pow(x))
}

/// `b^(a^true) => (a => b)^true`.
pub fn pow_tauto_to_tauto_imply<A: Prop, B: Prop>(
    x: Pow<B, Tauto<A>>
) -> Tauto<Imply<A, B>> {
    let y: Imply<Tauto<A>, Tauto<Tauto<A>>> = Rc::new(move |x| pow_lift(x));
    let x = hooo_imply(tauto_imply_pow(pow_lift(x)));
    hooo_rev_imply(imply::transitivity(y, x))
}

/// `b^(a^true) => b^a`.
pub fn pow_tauto_to_pow<A: Prop, B: Prop>(
    x: Pow<B, Tauto<A>>
) -> Pow<B, A> {
    tauto_imply_to_pow(pow_tauto_to_tauto_imply(x))
}

/// `b^a => b^(a^true)`.
pub fn pow_to_pow_tauto<A: Prop, B: Prop>(
    x: Pow<B, A>
) -> Pow<B, Tauto<A>> {
    tauto_imply_to_pow_tauto(pow_to_tauto_imply(x))
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
    fn check5<A: Prop, B: Prop, C: Prop>() {pow_eq::<Imply<Pow<A, C>, Pow<B, C>>, Pow<Imply<A, B>, C>>()}
    fn check6<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, And<A, B>>, Or<Pow<C, A>, Pow<C, B>>>()}
    fn check7<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Or<A, B>>, And<Pow<C, A>, Pow<C, B>>>()}
    fn check8<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Eq<A, B>>, Not<Eq<Pow<C, A>, Pow<C, B>>>>()}
    fn check9<A: Prop, B: Prop, C: Prop>() {pow_eq::<Pow<C, Imply<A, B>>, Not<Imply<Pow<C, B>, Pow<C, A>>>>()}
}
